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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4114, .m_capacity = 4114, .m_length = 4060, .m_data = "The `grind_pattern` command can be used to manually select a pattern for theorem instantiation.\nEnabling the option `trace.grind.ematch.instance` causes `grind` to print a trace message for each\ntheorem instance it generates, which can be helpful when determining patterns.\n\nWhen multiple patterns are specified together, all of them must match in the current context before\n`grind` attempts to instantiate the theorem. This is referred to as a *multi-pattern*.\nThis is useful for theorems such as transitivity rules, where multiple premises must be simultaneously\npresent for the rule to apply.\n\nIn the following example, `R` is a transitive binary relation over `Int`.\n```\nopaque R : Int → Int → Prop\naxiom Rtrans {x y z : Int} : R x y → R y z → R x z\n```\nTo use the fact that `R` is transitive, `grind` must already be able to satisfy both premises.\nThis is represented using a multi-pattern:\n```\ngrind_pattern Rtrans => R x y, R y z\n\nexample {a b c d} : R a b → R b c → R c d → R a d := by\n  grind\n```\nThe multi-pattern `R x y`, `R y z` instructs `grind` to instantiate `Rtrans` only when both `R x y`\nand `R y z` are available in the context. In the example, `grind` applies `Rtrans` to derive `R a c`\nfrom `R a b` and `R b c`, and can then repeat the same reasoning to deduce `R a d` from `R a c` and\n`R c d`.\n\nYou can add constraints to restrict theorem instantiation. For example:\n```\ngrind_pattern extract_extract => (as.extract i j).extract k l where\n  as =/= #[]\n```\nThe constraint instructs `grind` to instantiate the theorem only if `as` is **not** definitionally equal\nto `#[]`.\n\n## Constraints\n\n- `x =/= term`: The term bound to `x` (one of the theorem parameters) is **not** definitionally equal to `term`.\n  The term may contain holes (i.e., `_`).\n\n- `x =\?= term`: The term bound to `x` is definitionally equal to `term`.\n  The term may contain holes (i.e., `_`).\n\n- `size x < n`: The term bound to `x` has size less than `n`. Implicit arguments\nand binder types are ignored when computing the size.\n\n- `depth x < n`: The term bound to `x` has depth less than `n`.\n\n- `is_ground x`: The term bound to `x` does not contain local variables or meta-variables.\n\n- `is_value x`: The term bound to `x` is a value. That is, it is a constructor fully applied to value arguments,\na literal (`Nat`, `Int`, `String`, etc.), or a lambda `fun x => t`.\n\n- `is_strict_value x`: Similar to `is_value`, but without lambdas.\n\n- `not_value x`: The term bound to `x` is a **not** value (see `is_value`).\n\n- `not_strict_value x`: Similar to `not_value`, but without lambdas.\n\n- `gen < n`: The theorem instance has generation less than `n`. Recall that each term is assigned a\ngeneration, and terms produced by theorem instantiation have a generation that is one greater than\nthe maximal generation of all the terms used to instantiate the theorem. This constraint complements\nthe `gen` option available in `grind`.\n\n- `max_insts < n`: A new instance is generated only if less than `n` instances have been generated so far.\n\n- `guard e`: The instantiation is delayed until `grind` learns that `e` is `true` in this state.\n\n- `check e`: Similar to `guard e`, but `grind` checks whether `e` is implied by its current state by\nassuming `¬ e` and trying to deduce an inconsistency.\n\n## Example\n\nConsider the following example where `f` is a monotonic function\n```\nopaque f : Nat → Nat\naxiom fMono : x ≤ y → f x ≤ f y\n```\nand you want to instruct `grind` to instantiate `fMono` for every pair of terms `f x` and `f y` when\n`x ≤ y` and `x` is **not** definitionally equal to `y`. You can use\n```\ngrind_pattern fMono => f x, f y where\n  guard x ≤ y\n  x =/= y\n```\nThen, in the following example, only three instances are generated.\n```\n/--\ntrace: [grind.ematch.instance] fMono: a ≤ f a → f a ≤ f (f a)\n[grind.ematch.instance] fMono: f a ≤ f (f a) → f (f a) ≤ f (f (f a))\n[grind.ematch.instance] fMono: a ≤ f (f a) → f a ≤ f (f (f a))\n-/\n#guard_msgs in\nexample : f b = f c → a ≤ f a → f (f a) ≤ f (f (f a)) := by\n  set_option trace.grind.ematch.instance true in\n  grind\n```\n"};
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1(){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___boxed(lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1();
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3(){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_590_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___closed__0));
v___x_591_ = l_Lean_addBuiltinDocString(v___x_589_, v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___boxed(lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3();
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter(lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__0));
v___x_626_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__7));
v___x_627_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_625_, v___x_626_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter___boxed(lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Parser_Command_GrindCnstr_isValue_formatter(v_a_628_, v_a_629_, v_a_630_, v_a_631_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7(){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_643_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_644_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5));
v___x_645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1));
v___x_646_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___boxed), 5, 0);
v___x_647_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_643_, v___x_644_, v___x_645_, v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___boxed(lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7();
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter(lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__0));
v___x_674_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__3));
v___x_675_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_673_, v___x_674_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___boxed(lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter(v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11(){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_690_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_691_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1));
v___x_692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0));
v___x_693_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___boxed), 5, 0);
v___x_694_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_690_, v___x_691_, v___x_692_, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___boxed(lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11();
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_formatter(lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__0));
v___x_721_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__3));
v___x_722_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_720_, v___x_721_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_formatter___boxed(lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Parser_Command_GrindCnstr_notValue_formatter(v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15(){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_737_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_738_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1));
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0));
v___x_740_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___boxed), 5, 0);
v___x_741_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_737_, v___x_738_, v___x_739_, v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___boxed(lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15();
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter(lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__0));
v___x_768_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__3));
v___x_769_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_767_, v___x_768_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___boxed(lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter(v_a_770_, v_a_771_, v_a_772_, v_a_773_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19(){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_784_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_785_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1));
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0));
v___x_787_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___boxed), 5, 0);
v___x_788_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_784_, v___x_785_, v___x_786_, v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___boxed(lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19();
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_formatter(lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__0));
v___x_815_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__3));
v___x_816_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_814_, v___x_815_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_formatter___boxed(lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Parser_Command_GrindCnstr_isGround_formatter(v_a_817_, v_a_818_, v_a_819_, v_a_820_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23(){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_831_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_832_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1));
v___x_833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0));
v___x_834_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___boxed), 5, 0);
v___x_835_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_831_, v___x_832_, v___x_833_, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___boxed(lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23();
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter(lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__0));
v___x_874_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__8));
v___x_875_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_873_, v___x_874_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___boxed(lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter(v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27(){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_890_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_891_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1));
v___x_892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0));
v___x_893_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___boxed), 5, 0);
v___x_894_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_890_, v___x_891_, v___x_892_, v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___boxed(lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27();
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_formatter(lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_920_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__0));
v___x_921_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__3));
v___x_922_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_920_, v___x_921_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___boxed(lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Parser_Command_GrindCnstr_depthLt_formatter(v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31(){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_937_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_938_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1));
v___x_939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0));
v___x_940_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___boxed), 5, 0);
v___x_941_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_937_, v___x_938_, v___x_939_, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___boxed(lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31();
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_formatter(lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__0));
v___x_968_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__3));
v___x_969_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_967_, v___x_968_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_formatter___boxed(lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Parser_Command_GrindCnstr_genLt_formatter(v_a_970_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35(){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_984_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_985_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1));
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0));
v___x_987_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___boxed), 5, 0);
v___x_988_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_984_, v___x_985_, v___x_986_, v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___boxed(lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35();
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter(lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__0));
v___x_1015_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__3));
v___x_1016_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1014_, v___x_1015_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___boxed(lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter(v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39(){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1031_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1032_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1));
v___x_1033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0));
v___x_1034_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___boxed), 5, 0);
v___x_1035_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1031_, v___x_1032_, v___x_1033_, v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___boxed(lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39();
return v_res_1037_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__3));
v___x_1055_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 5, 0);
v___x_1056_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1056_, 0, v___x_1055_);
lean_closure_set(v___x_1056_, 1, v___x_1054_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4);
v___x_1058_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__1));
v___x_1059_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1059_, 0, v___x_1058_);
lean_closure_set(v___x_1059_, 1, v___x_1057_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1060_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5, &l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5);
v___x_1061_ = lean_unsigned_to_nat(1024u);
v___x_1062_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__1));
v___x_1063_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1063_, 0, v___x_1062_);
lean_closure_set(v___x_1063_, 1, v___x_1061_);
lean_closure_set(v___x_1063_, 2, v___x_1060_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_guard_formatter(lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__0));
v___x_1070_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6, &l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6);
v___x_1071_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1069_, v___x_1070_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_guard_formatter___boxed(lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Parser_Command_GrindCnstr_guard_formatter(v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43(){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1086_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1087_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__1));
v___x_1088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0));
v___x_1089_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_guard_formatter___boxed), 5, 0);
v___x_1090_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1086_, v___x_1087_, v___x_1088_, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___boxed(lean_object* v_a_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43();
return v_res_1092_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4);
v___x_1105_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__1));
v___x_1106_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1106_, 0, v___x_1105_);
lean_closure_set(v___x_1106_, 1, v___x_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1107_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2, &l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2);
v___x_1108_ = lean_unsigned_to_nat(1024u);
v___x_1109_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check___closed__1));
v___x_1110_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1110_, 0, v___x_1109_);
lean_closure_set(v___x_1110_, 1, v___x_1108_);
lean_closure_set(v___x_1110_, 2, v___x_1107_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_check_formatter(lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__0));
v___x_1117_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3, &l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3_once, _init_l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3);
v___x_1118_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1116_, v___x_1117_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_check_formatter___boxed(lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Parser_Command_GrindCnstr_check_formatter(v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47(){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1133_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1134_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check___closed__1));
v___x_1135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0));
v___x_1136_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_check_formatter___boxed), 5, 0);
v___x_1137_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1133_, v___x_1134_, v___x_1135_, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___boxed(lean_object* v_a_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47();
return v_res_1139_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4);
v___x_1155_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__3));
v___x_1156_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1156_, 0, v___x_1155_);
lean_closure_set(v___x_1156_, 1, v___x_1154_);
return v___x_1156_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1157_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4, &l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4);
v___x_1158_ = lean_unsigned_to_nat(1024u);
v___x_1159_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1));
v___x_1160_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1160_, 0, v___x_1159_);
lean_closure_set(v___x_1160_, 1, v___x_1158_);
lean_closure_set(v___x_1160_, 2, v___x_1157_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter(lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__0));
v___x_1167_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5, &l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5);
v___x_1168_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1166_, v___x_1167_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___boxed(lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter(v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51(){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1183_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1184_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1));
v___x_1185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0));
v___x_1186_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___boxed), 5, 0);
v___x_1187_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1183_, v___x_1184_, v___x_1185_, v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___boxed(lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51();
return v_res_1189_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4);
v___x_1205_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__3));
v___x_1206_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1206_, 0, v___x_1205_);
lean_closure_set(v___x_1206_, 1, v___x_1204_);
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1207_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4, &l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4);
v___x_1208_ = lean_unsigned_to_nat(1024u);
v___x_1209_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1));
v___x_1210_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1210_, 0, v___x_1209_);
lean_closure_set(v___x_1210_, 1, v___x_1208_);
lean_closure_set(v___x_1210_, 2, v___x_1207_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_formatter(lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__0));
v___x_1217_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5, &l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5);
v___x_1218_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1216_, v___x_1217_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_formatter___boxed(lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Parser_Command_GrindCnstr_defEq_formatter(v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55(){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1233_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1234_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1));
v___x_1235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0));
v___x_1236_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___boxed), 5, 0);
v___x_1237_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1233_, v___x_1234_, v___x_1235_, v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___boxed(lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55();
return v_res_1239_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___boxed), 5, 0);
v___x_1241_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___boxed), 5, 0);
v___x_1242_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1242_, 0, v___x_1241_);
lean_closure_set(v___x_1242_, 1, v___x_1240_);
return v___x_1242_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0);
v___x_1244_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_check_formatter___boxed), 5, 0);
v___x_1245_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1245_, 0, v___x_1244_);
lean_closure_set(v___x_1245_, 1, v___x_1243_);
return v___x_1245_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1);
v___x_1247_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_guard_formatter___boxed), 5, 0);
v___x_1248_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1248_, 0, v___x_1247_);
lean_closure_set(v___x_1248_, 1, v___x_1246_);
return v___x_1248_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2);
v___x_1250_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___boxed), 5, 0);
v___x_1251_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1251_, 0, v___x_1250_);
lean_closure_set(v___x_1251_, 1, v___x_1249_);
return v___x_1251_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3);
v___x_1253_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___boxed), 5, 0);
v___x_1254_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1254_, 0, v___x_1253_);
lean_closure_set(v___x_1254_, 1, v___x_1252_);
return v___x_1254_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4);
v___x_1256_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___boxed), 5, 0);
v___x_1257_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1257_, 0, v___x_1256_);
lean_closure_set(v___x_1257_, 1, v___x_1255_);
return v___x_1257_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5);
v___x_1259_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___boxed), 5, 0);
v___x_1260_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1260_, 0, v___x_1259_);
lean_closure_set(v___x_1260_, 1, v___x_1258_);
return v___x_1260_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6);
v___x_1262_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___boxed), 5, 0);
v___x_1263_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1263_, 0, v___x_1262_);
lean_closure_set(v___x_1263_, 1, v___x_1261_);
return v___x_1263_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7);
v___x_1265_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___boxed), 5, 0);
v___x_1266_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1266_, 0, v___x_1265_);
lean_closure_set(v___x_1266_, 1, v___x_1264_);
return v___x_1266_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8);
v___x_1268_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___boxed), 5, 0);
v___x_1269_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1269_, 0, v___x_1268_);
lean_closure_set(v___x_1269_, 1, v___x_1267_);
return v___x_1269_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9);
v___x_1271_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___boxed), 5, 0);
v___x_1272_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1272_, 0, v___x_1271_);
lean_closure_set(v___x_1272_, 1, v___x_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter(lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___boxed), 5, 0);
v___x_1279_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10);
v___x_1280_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1278_, v___x_1279_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___boxed(lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_Parser_Command_grindPatternCnstr_formatter(v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
return v_res_1286_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPatternCnstr_formatter___boxed), 5, 0);
v___x_1297_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
v___x_1298_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1298_, 0, v___x_1297_);
lean_closure_set(v___x_1298_, 1, v___x_1296_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2, &l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2);
v___x_1300_ = lean_alloc_closure((void*)(l_Lean_Parser_many1Indent_formatter___boxed), 6, 1);
lean_closure_set(v___x_1300_, 0, v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3, &l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3);
v___x_1302_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__1));
v___x_1303_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1303_, 0, v___x_1302_);
lean_closure_set(v___x_1303_, 1, v___x_1301_);
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1304_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4, &l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4);
v___x_1305_ = lean_unsigned_to_nat(1024u);
v___x_1306_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs___closed__1));
v___x_1307_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1307_, 0, v___x_1306_);
lean_closure_set(v___x_1307_, 1, v___x_1305_);
lean_closure_set(v___x_1307_, 2, v___x_1304_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstrs_formatter(lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__0));
v___x_1314_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5, &l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5);
v___x_1315_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1313_, v___x_1314_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstrs_formatter___boxed(lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_Parser_Command_grindPatternCnstrs_formatter(v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61(){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1329_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1330_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs___closed__1));
v___x_1331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0));
v___x_1332_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPatternCnstrs_formatter___boxed), 5, 0);
v___x_1333_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1329_, v___x_1330_, v___x_1331_, v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___boxed(lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61();
return v_res_1335_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__11(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPatternCnstrs_formatter___boxed), 5, 0);
v___x_1368_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__12(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__11, &l_Lean_Parser_Command_grindPattern_formatter___closed__11_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__11);
v___x_1370_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_formatter___closed__10));
v___x_1371_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1371_, 0, v___x_1370_);
lean_closure_set(v___x_1371_, 1, v___x_1369_);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__13(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__12, &l_Lean_Parser_Command_grindPattern_formatter___closed__12_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__12);
v___x_1373_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_formatter___closed__8));
v___x_1374_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1374_, 0, v___x_1373_);
lean_closure_set(v___x_1374_, 1, v___x_1372_);
return v___x_1374_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__14(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__13, &l_Lean_Parser_Command_grindPattern_formatter___closed__13_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__13);
v___x_1376_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2));
v___x_1377_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1377_, 0, v___x_1376_);
lean_closure_set(v___x_1377_, 1, v___x_1375_);
return v___x_1377_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__15(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__14, &l_Lean_Parser_Command_grindPattern_formatter___closed__14_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__14);
v___x_1379_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_formatter___closed__7));
v___x_1380_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1380_, 0, v___x_1379_);
lean_closure_set(v___x_1380_, 1, v___x_1378_);
return v___x_1380_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__16(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__15, &l_Lean_Parser_Command_grindPattern_formatter___closed__15_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__15);
v___x_1382_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_formatter___closed__2));
v___x_1383_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1383_, 0, v___x_1382_);
lean_closure_set(v___x_1383_, 1, v___x_1381_);
return v___x_1383_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__17(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__16, &l_Lean_Parser_Command_grindPattern_formatter___closed__16_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__16);
v___x_1385_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_formatter___closed__1));
v___x_1386_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1386_, 0, v___x_1385_);
lean_closure_set(v___x_1386_, 1, v___x_1384_);
return v___x_1386_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__18(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1387_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__17, &l_Lean_Parser_Command_grindPattern_formatter___closed__17_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__17);
v___x_1388_ = lean_unsigned_to_nat(1024u);
v___x_1389_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_1390_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1390_, 0, v___x_1389_);
lean_closure_set(v___x_1390_, 1, v___x_1388_);
lean_closure_set(v___x_1390_, 2, v___x_1387_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPattern_formatter(lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_formatter___closed__0));
v___x_1397_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__18, &l_Lean_Parser_Command_grindPattern_formatter___closed__18_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__18);
v___x_1398_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1396_, v___x_1397_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPattern_formatter___boxed(lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Parser_Command_grindPattern_formatter(v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65(){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1412_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1413_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_1414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0));
v___x_1415_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPattern_formatter___boxed), 5, 0);
v___x_1416_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1412_, v___x_1413_, v___x_1414_, v___x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___boxed(lean_object* v_a_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65();
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer(lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__0));
v___x_1451_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__7));
v___x_1452_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1450_, v___x_1451_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___boxed(lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer(v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69(){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1468_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1469_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5));
v___x_1470_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1));
v___x_1471_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___boxed), 5, 0);
v___x_1472_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1468_, v___x_1469_, v___x_1470_, v___x_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___boxed(lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69();
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer(lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__0));
v___x_1499_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__3));
v___x_1500_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1498_, v___x_1499_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___boxed(lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer(v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73(){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1515_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1516_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1));
v___x_1517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0));
v___x_1518_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___boxed), 5, 0);
v___x_1519_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1515_, v___x_1516_, v___x_1517_, v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___boxed(lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73();
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer(lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__0));
v___x_1546_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__3));
v___x_1547_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1545_, v___x_1546_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___boxed(lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer(v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77(){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1562_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1563_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1));
v___x_1564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0));
v___x_1565_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___boxed), 5, 0);
v___x_1566_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1562_, v___x_1563_, v___x_1564_, v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___boxed(lean_object* v_a_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77();
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer(lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__0));
v___x_1593_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__3));
v___x_1594_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1592_, v___x_1593_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___boxed(lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer(v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81(){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1609_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1610_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1));
v___x_1611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0));
v___x_1612_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___boxed), 5, 0);
v___x_1613_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1609_, v___x_1610_, v___x_1611_, v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___boxed(lean_object* v_a_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81();
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer(lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__0));
v___x_1640_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__3));
v___x_1641_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1639_, v___x_1640_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___boxed(lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer(v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85(){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1656_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1657_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1));
v___x_1658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0));
v___x_1659_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___boxed), 5, 0);
v___x_1660_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1656_, v___x_1657_, v___x_1658_, v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___boxed(lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85();
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer(lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__0));
v___x_1699_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__8));
v___x_1700_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1698_, v___x_1699_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___boxed(lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer(v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89(){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1715_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1716_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1));
v___x_1717_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0));
v___x_1718_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___boxed), 5, 0);
v___x_1719_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1715_, v___x_1716_, v___x_1717_, v___x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___boxed(lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89();
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer(lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__0));
v___x_1746_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__3));
v___x_1747_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1745_, v___x_1746_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___boxed(lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer(v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93(){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1762_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1763_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1));
v___x_1764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0));
v___x_1765_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___boxed), 5, 0);
v___x_1766_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1762_, v___x_1763_, v___x_1764_, v___x_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___boxed(lean_object* v_a_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93();
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer(lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__0));
v___x_1793_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__3));
v___x_1794_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1792_, v___x_1793_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___boxed(lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer(v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97(){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1809_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1810_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1));
v___x_1811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0));
v___x_1812_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___boxed), 5, 0);
v___x_1813_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1809_, v___x_1810_, v___x_1811_, v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___boxed(lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97();
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer(lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__0));
v___x_1840_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__3));
v___x_1841_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1839_, v___x_1840_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___boxed(lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer(v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101(){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1856_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1857_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1));
v___x_1858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0));
v___x_1859_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___boxed), 5, 0);
v___x_1860_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1856_, v___x_1857_, v___x_1858_, v___x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___boxed(lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101();
return v_res_1862_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__3));
v___x_1880_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
v___x_1881_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1881_, 0, v___x_1880_);
lean_closure_set(v___x_1881_, 1, v___x_1879_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4);
v___x_1883_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__1));
v___x_1884_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1884_, 0, v___x_1883_);
lean_closure_set(v___x_1884_, 1, v___x_1882_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1885_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5, &l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5);
v___x_1886_ = lean_unsigned_to_nat(1024u);
v___x_1887_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__1));
v___x_1888_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1888_, 0, v___x_1887_);
lean_closure_set(v___x_1888_, 1, v___x_1886_);
lean_closure_set(v___x_1888_, 2, v___x_1885_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer(lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__0));
v___x_1895_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6, &l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6);
v___x_1896_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1894_, v___x_1895_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___boxed(lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer(v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105(){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1911_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1912_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__1));
v___x_1913_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0));
v___x_1914_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___boxed), 5, 0);
v___x_1915_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1911_, v___x_1912_, v___x_1913_, v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___boxed(lean_object* v_a_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105();
return v_res_1917_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4);
v___x_1930_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__1));
v___x_1931_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1931_, 0, v___x_1930_);
lean_closure_set(v___x_1931_, 1, v___x_1929_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1932_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2, &l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2);
v___x_1933_ = lean_unsigned_to_nat(1024u);
v___x_1934_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check___closed__1));
v___x_1935_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1935_, 0, v___x_1934_);
lean_closure_set(v___x_1935_, 1, v___x_1933_);
lean_closure_set(v___x_1935_, 2, v___x_1932_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_check_parenthesizer(lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__0));
v___x_1942_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3, &l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3_once, _init_l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3);
v___x_1943_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1941_, v___x_1942_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___boxed(lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Parser_Command_GrindCnstr_check_parenthesizer(v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109(){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1958_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1959_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check___closed__1));
v___x_1960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0));
v___x_1961_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___boxed), 5, 0);
v___x_1962_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1958_, v___x_1959_, v___x_1960_, v___x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___boxed(lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109();
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0(lean_object* v___x_1965_, lean_object* v___x_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_1965_, v___x_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0___boxed(lean_object* v___x_1973_, lean_object* v___x_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0(v___x_1973_, v___x_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
return v_res_1980_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___f_1994_; lean_object* v___x_1995_; 
v___x_1993_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4);
v___f_1994_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__2));
v___x_1995_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1995_, 0, v___f_1994_);
lean_closure_set(v___x_1995_, 1, v___x_1993_);
return v___x_1995_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1996_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3, &l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3);
v___x_1997_ = lean_unsigned_to_nat(1024u);
v___x_1998_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1));
v___x_1999_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1999_, 0, v___x_1998_);
lean_closure_set(v___x_1999_, 1, v___x_1997_);
lean_closure_set(v___x_1999_, 2, v___x_1996_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer(lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__0));
v___x_2006_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4, &l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4);
v___x_2007_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2005_, v___x_2006_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___boxed(lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer(v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113(){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2022_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2023_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1));
v___x_2024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0));
v___x_2025_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___boxed), 5, 0);
v___x_2026_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2022_, v___x_2023_, v___x_2024_, v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___boxed(lean_object* v_a_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113();
return v_res_2028_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___f_2042_; lean_object* v___x_2043_; 
v___x_2041_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4);
v___f_2042_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__2));
v___x_2043_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2043_, 0, v___f_2042_);
lean_closure_set(v___x_2043_, 1, v___x_2041_);
return v___x_2043_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2044_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3, &l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3);
v___x_2045_ = lean_unsigned_to_nat(1024u);
v___x_2046_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1));
v___x_2047_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2047_, 0, v___x_2046_);
lean_closure_set(v___x_2047_, 1, v___x_2045_);
lean_closure_set(v___x_2047_, 2, v___x_2044_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer(lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__0));
v___x_2054_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4, &l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4);
v___x_2055_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2053_, v___x_2054_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___boxed(lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer(v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117(){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2070_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2071_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1));
v___x_2072_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0));
v___x_2073_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___boxed), 5, 0);
v___x_2074_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2070_, v___x_2071_, v___x_2072_, v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___boxed(lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117();
return v_res_2076_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___boxed), 5, 0);
v___x_2078_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___boxed), 5, 0);
v___x_2079_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2079_, 0, v___x_2078_);
lean_closure_set(v___x_2079_, 1, v___x_2077_);
return v___x_2079_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0);
v___x_2081_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___boxed), 5, 0);
v___x_2082_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2082_, 0, v___x_2081_);
lean_closure_set(v___x_2082_, 1, v___x_2080_);
return v___x_2082_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1);
v___x_2084_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___boxed), 5, 0);
v___x_2085_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2085_, 0, v___x_2084_);
lean_closure_set(v___x_2085_, 1, v___x_2083_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2);
v___x_2087_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___boxed), 5, 0);
v___x_2088_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2088_, 0, v___x_2087_);
lean_closure_set(v___x_2088_, 1, v___x_2086_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3);
v___x_2090_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___boxed), 5, 0);
v___x_2091_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2091_, 0, v___x_2090_);
lean_closure_set(v___x_2091_, 1, v___x_2089_);
return v___x_2091_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4);
v___x_2093_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___boxed), 5, 0);
v___x_2094_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2094_, 0, v___x_2093_);
lean_closure_set(v___x_2094_, 1, v___x_2092_);
return v___x_2094_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5);
v___x_2096_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___boxed), 5, 0);
v___x_2097_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2097_, 0, v___x_2096_);
lean_closure_set(v___x_2097_, 1, v___x_2095_);
return v___x_2097_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6);
v___x_2099_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___boxed), 5, 0);
v___x_2100_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2100_, 0, v___x_2099_);
lean_closure_set(v___x_2100_, 1, v___x_2098_);
return v___x_2100_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2101_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7);
v___x_2102_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___boxed), 5, 0);
v___x_2103_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2103_, 0, v___x_2102_);
lean_closure_set(v___x_2103_, 1, v___x_2101_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8);
v___x_2105_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___boxed), 5, 0);
v___x_2106_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2106_, 0, v___x_2105_);
lean_closure_set(v___x_2106_, 1, v___x_2104_);
return v___x_2106_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9);
v___x_2108_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___boxed), 5, 0);
v___x_2109_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2109_, 0, v___x_2108_);
lean_closure_set(v___x_2109_, 1, v___x_2107_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer(lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2115_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___boxed), 5, 0);
v___x_2116_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10);
v___x_2117_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_2115_, v___x_2116_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___boxed(lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_Parser_Command_grindPatternCnstr_parenthesizer(v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
return v_res_2123_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___boxed), 5, 0);
v___x_2135_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__2));
v___x_2136_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2136_, 0, v___x_2135_);
lean_closure_set(v___x_2136_, 1, v___x_2134_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3, &l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3);
v___x_2138_ = lean_alloc_closure((void*)(l_Lean_Parser_many1Indent_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2138_, 0, v___x_2137_);
return v___x_2138_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2139_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4, &l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4);
v___x_2140_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__1));
v___x_2141_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2141_, 0, v___x_2140_);
lean_closure_set(v___x_2141_, 1, v___x_2139_);
return v___x_2141_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2142_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5, &l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5);
v___x_2143_ = lean_unsigned_to_nat(1024u);
v___x_2144_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs___closed__1));
v___x_2145_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2145_, 0, v___x_2144_);
lean_closure_set(v___x_2145_, 1, v___x_2143_);
lean_closure_set(v___x_2145_, 2, v___x_2142_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer(lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__0));
v___x_2152_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6, &l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6);
v___x_2153_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2151_, v___x_2152_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___boxed(lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer(v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
lean_dec(v_a_2157_);
lean_dec_ref(v_a_2156_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123(){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2167_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2168_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs___closed__1));
v___x_2169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0));
v___x_2170_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___boxed), 5, 0);
v___x_2171_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2167_, v___x_2168_, v___x_2169_, v___x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___boxed(lean_object* v_a_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123();
return v_res_2173_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___boxed), 5, 0);
v___x_2206_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11);
v___x_2208_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__10));
v___x_2209_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2209_, 0, v___x_2208_);
lean_closure_set(v___x_2209_, 1, v___x_2207_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12);
v___x_2211_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__8));
v___x_2212_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2212_, 0, v___x_2211_);
lean_closure_set(v___x_2212_, 1, v___x_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13);
v___x_2214_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2));
v___x_2215_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2215_, 0, v___x_2214_);
lean_closure_set(v___x_2215_, 1, v___x_2213_);
return v___x_2215_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14);
v___x_2217_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__7));
v___x_2218_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2218_, 0, v___x_2217_);
lean_closure_set(v___x_2218_, 1, v___x_2216_);
return v___x_2218_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15);
v___x_2220_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__2));
v___x_2221_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2221_, 0, v___x_2220_);
lean_closure_set(v___x_2221_, 1, v___x_2219_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16);
v___x_2223_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__1));
v___x_2224_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2224_, 0, v___x_2223_);
lean_closure_set(v___x_2224_, 1, v___x_2222_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2225_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17);
v___x_2226_ = lean_unsigned_to_nat(1024u);
v___x_2227_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_2228_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2228_, 0, v___x_2227_);
lean_closure_set(v___x_2228_, 1, v___x_2226_);
lean_closure_set(v___x_2228_, 2, v___x_2225_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer(lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__0));
v___x_2235_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18);
v___x_2236_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2234_, v___x_2235_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___boxed(lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_Parser_Command_grindPattern_parenthesizer(v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127(){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2250_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2251_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_2252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0));
v___x_2253_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPattern_parenthesizer___boxed), 5, 0);
v___x_2254_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2250_, v___x_2251_, v___x_2252_, v___x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___boxed(lean_object* v_a_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127();
return v_res_2256_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__2(void){
_start:
{
uint8_t v___x_2263_; uint8_t v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2263_ = 0;
v___x_2264_ = 1;
v___x_2265_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__1));
v___x_2266_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__0));
v___x_2267_ = l_Lean_Parser_mkAntiquot(v___x_2266_, v___x_2265_, v___x_2264_, v___x_2263_);
return v___x_2267_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__4(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__3));
v___x_2270_ = l_Lean_Parser_symbol(v___x_2269_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__5(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = l_Lean_Parser_ident;
v___x_2272_ = l_Lean_Parser_many(v___x_2271_);
return v___x_2272_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__7(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__6));
v___x_2275_ = l_Lean_Parser_symbol(v___x_2274_);
return v___x_2275_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__8(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__5, &l_Lean_Parser_Command_initGrindNorm___closed__5_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__5);
v___x_2277_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__7, &l_Lean_Parser_Command_initGrindNorm___closed__7_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__7);
v___x_2278_ = l_Lean_Parser_andthen(v___x_2277_, v___x_2276_);
return v___x_2278_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__9(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__8, &l_Lean_Parser_Command_initGrindNorm___closed__8_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__8);
v___x_2280_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__5, &l_Lean_Parser_Command_initGrindNorm___closed__5_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__5);
v___x_2281_ = l_Lean_Parser_andthen(v___x_2280_, v___x_2279_);
return v___x_2281_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__10(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__9, &l_Lean_Parser_Command_initGrindNorm___closed__9_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__9);
v___x_2283_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__4, &l_Lean_Parser_Command_initGrindNorm___closed__4_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__4);
v___x_2284_ = l_Lean_Parser_andthen(v___x_2283_, v___x_2282_);
return v___x_2284_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__11(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2285_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__10, &l_Lean_Parser_Command_initGrindNorm___closed__10_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__10);
v___x_2286_ = lean_unsigned_to_nat(1024u);
v___x_2287_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__1));
v___x_2288_ = l_Lean_Parser_leadingNode(v___x_2287_, v___x_2286_, v___x_2285_);
return v___x_2288_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__12(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__11, &l_Lean_Parser_Command_initGrindNorm___closed__11_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__11);
v___x_2290_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__2, &l_Lean_Parser_Command_initGrindNorm___closed__2_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__2);
v___x_2291_ = l_Lean_Parser_withAntiquot(v___x_2290_, v___x_2289_);
return v___x_2291_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__13(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__12, &l_Lean_Parser_Command_initGrindNorm___closed__12_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__12);
v___x_2293_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__1));
v___x_2294_ = l_Lean_Parser_withCache(v___x_2293_, v___x_2292_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm(void){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__13, &l_Lean_Parser_Command_initGrindNorm___closed__13_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__13);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1(){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__1));
v___x_2298_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__1));
v___x_2299_ = l_Lean_Parser_Command_initGrindNorm;
v___x_2300_ = lean_unsigned_to_nat(1000u);
v___x_2301_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_2297_, v___x_2298_, v___x_2299_, v___x_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1___boxed(lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1();
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_initGrindNorm_formatter(lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2335_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm_formatter___closed__0));
v___x_2336_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm_formatter___closed__7));
v___x_2337_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2335_, v___x_2336_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_initGrindNorm_formatter___boxed(lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_Parser_Command_initGrindNorm_formatter(v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5(){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2351_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2352_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__1));
v___x_2353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0));
v___x_2354_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_initGrindNorm_formatter___boxed), 5, 0);
v___x_2355_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2351_, v___x_2352_, v___x_2353_, v___x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___boxed(lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5();
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer(lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__0));
v___x_2390_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__7));
v___x_2391_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2389_, v___x_2390_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer___boxed(lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_Parser_Command_initGrindNorm_parenthesizer(v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9(){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2405_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2406_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__1));
v___x_2407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0));
v___x_2408_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_initGrindNorm_parenthesizer___boxed), 5, 0);
v___x_2409_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2405_, v___x_2406_, v___x_2407_, v___x_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___boxed(lean_object* v_a_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9();
return v_res_2411_;
}
}
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
