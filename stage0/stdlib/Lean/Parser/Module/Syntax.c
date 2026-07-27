// Lean compiler output
// Module: Lean.Parser.Module.Syntax
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
lean_object* l_Lean_ppLine_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_commandParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_skip;
extern lean_object* l_Lean_Parser_identWithPartialTrailingDot;
lean_object* l_Lean_Parser_many(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_commandParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Module_moduleTk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Module_moduleTk___closed__0 = (const lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value;
static const lean_string_object l_Lean_Parser_Module_moduleTk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Module_moduleTk___closed__1 = (const lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value;
static const lean_string_object l_Lean_Parser_Module_moduleTk___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l_Lean_Parser_Module_moduleTk___closed__2 = (const lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value;
static const lean_string_object l_Lean_Parser_Module_moduleTk___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "moduleTk"};
static const lean_object* l_Lean_Parser_Module_moduleTk___closed__3 = (const lean_object*)&l_Lean_Parser_Module_moduleTk___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Module_moduleTk___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_moduleTk___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_moduleTk___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_moduleTk___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 239, 28, 252, 21, 233, 71, 221)}};
static const lean_object* l_Lean_Parser_Module_moduleTk___closed__4 = (const lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value;
static lean_once_cell_t l_Lean_Parser_Module_moduleTk___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_moduleTk___closed__5;
static const lean_string_object l_Lean_Parser_Module_moduleTk___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_Parser_Module_moduleTk___closed__6 = (const lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value;
static lean_once_cell_t l_Lean_Parser_Module_moduleTk___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_moduleTk___closed__7;
static lean_once_cell_t l_Lean_Parser_Module_moduleTk___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_moduleTk___closed__8;
static lean_once_cell_t l_Lean_Parser_Module_moduleTk___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_moduleTk___closed__9;
static lean_once_cell_t l_Lean_Parser_Module_moduleTk___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_moduleTk___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk;
static const lean_string_object l_Lean_Parser_Module_prelude___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "prelude"};
static const lean_object* l_Lean_Parser_Module_prelude___closed__0 = (const lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_prelude___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_prelude___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_prelude___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_prelude___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 6, 18, 235, 50, 88, 101, 248)}};
static const lean_object* l_Lean_Parser_Module_prelude___closed__1 = (const lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_prelude___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_prelude___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_prelude___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_prelude___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_prelude___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_prelude___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_prelude___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_prelude___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_prelude___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_prelude___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude;
static const lean_string_object l_Lean_Parser_Module_public___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lean_Parser_Module_public___closed__0 = (const lean_object*)&l_Lean_Parser_Module_public___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_public___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_public___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_public___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_public___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_public___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_object* l_Lean_Parser_Module_public___closed__1 = (const lean_object*)&l_Lean_Parser_Module_public___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_public___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_public___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_public___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_public___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_public___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_public___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_public___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_public___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_public___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_public___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public;
static const lean_string_object l_Lean_Parser_Module_meta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Parser_Module_meta___closed__0 = (const lean_object*)&l_Lean_Parser_Module_meta___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_meta___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_meta___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_meta___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_meta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_meta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 228, 64, 55, 26, 167, 248, 235)}};
static const lean_object* l_Lean_Parser_Module_meta___closed__1 = (const lean_object*)&l_Lean_Parser_Module_meta___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_meta___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_meta___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_meta___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_meta___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_meta___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_meta___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_meta___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_meta___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_meta___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_meta___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta;
static const lean_string_object l_Lean_Parser_Module_all___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lean_Parser_Module_all___closed__0 = (const lean_object*)&l_Lean_Parser_Module_all___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_all___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_all___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_all___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_all___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_all___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 73, 92, 3, 207, 252, 164, 131)}};
static const lean_object* l_Lean_Parser_Module_all___closed__1 = (const lean_object*)&l_Lean_Parser_Module_all___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_all___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_all___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_all___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_all___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_all___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_all___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_all___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_all___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_all___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_all___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all;
static const lean_string_object l_Lean_Parser_Module_import___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l_Lean_Parser_Module_import___closed__0 = (const lean_object*)&l_Lean_Parser_Module_import___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_import___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_import___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_import___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_import___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_import___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_object* l_Lean_Parser_Module_import___closed__1 = (const lean_object*)&l_Lean_Parser_Module_import___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__4;
static const lean_string_object l_Lean_Parser_Module_import___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "import "};
static const lean_object* l_Lean_Parser_Module_import___closed__5 = (const lean_object*)&l_Lean_Parser_Module_import___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__6;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__7;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__8;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__9;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__10;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__11;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__12;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__13;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__14;
static lean_once_cell_t l_Lean_Parser_Module_import___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import___closed__15;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import;
static const lean_string_object l_Lean_Parser_Module_header___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Parser_Module_header___closed__0 = (const lean_object*)&l_Lean_Parser_Module_header___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Module_header___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_header___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_header___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_header___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_header___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_header___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_header___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_header___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_object* l_Lean_Parser_Module_header___closed__1 = (const lean_object*)&l_Lean_Parser_Module_header___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__6;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__7;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__8;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__9;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__10;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__11;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__12;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__13;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__14;
static lean_once_cell_t l_Lean_Parser_Module_header___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header___closed__15;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header;
static const lean_closure_object l_Lean_Parser_Module_moduleTk_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__3_value),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_moduleTk_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Module_moduleTk_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Module_moduleTk_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value)} };
static const lean_object* l_Lean_Parser_Module_moduleTk_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Module_moduleTk_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_moduleTk_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_moduleTk_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Module_moduleTk_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 239, 28, 252, 21, 233, 71, 221)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 81, 79, 40, 155, 75, 46, 100)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Module_prelude_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value),((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_prelude_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Module_prelude_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Module_prelude_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_prelude_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Module_prelude_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_prelude_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_prelude_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_prelude_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Module_prelude_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 6, 18, 235, 50, 88, 101, 248)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 131, 178, 125, 52, 15, 11, 203)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Module_public_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__0_value),((lean_object*)&l_Lean_Parser_Module_public___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_public_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Module_public_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Module_public_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_public_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Module_public_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_public_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_public_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_public_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Module_public_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_public___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 212, 57, 147, 153, 56, 10, 5)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Module_meta_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__0_value),((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_meta_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Module_meta_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Module_meta_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_meta_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Module_meta_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_meta_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_meta_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_meta_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Module_meta_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_meta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 228, 64, 55, 26, 167, 248, 235)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 184, 202, 195, 54, 104, 118, 145)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Module_all_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__0_value),((lean_object*)&l_Lean_Parser_Module_all___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_all_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Module_all_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Module_all_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_all_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Module_all_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_all_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_all_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_all_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Module_all_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_all___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 73, 92, 3, 207, 252, 164, 131)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 99, 131, 63, 105, 143, 101, 58)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Module_import_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__0_value),((lean_object*)&l_Lean_Parser_Module_import___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_import_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Module_import_formatter___closed__0_value;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__1;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__2;
static const lean_closure_object l_Lean_Parser_Module_import_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__5_value)} };
static const lean_object* l_Lean_Parser_Module_import_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Module_import_formatter___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__6;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__7;
static const lean_closure_object l_Lean_Parser_Module_import_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Module_import_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_Module_import_formatter___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__9;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__10;
static lean_once_cell_t l_Lean_Parser_Module_import_formatter___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_formatter___closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_import___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 109, 123, 234, 127, 180, 211, 104)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Module_header_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_header___closed__0_value),((lean_object*)&l_Lean_Parser_Module_header___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_header_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Module_header_formatter___closed__0_value;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__1;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__2;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__6;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__7;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__8;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__9;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__10;
static lean_once_cell_t l_Lean_Parser_Module_header_formatter___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_formatter___closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_header___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 160, 40, 95, 57, 209, 137, 179)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___boxed(lean_object*);
static const lean_ctor_object l_Lean_Parser_Module_module_formatter___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Module_module_formatter___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module_formatter___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Module_module_formatter___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module_formatter___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Parser_Module_module_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module_formatter___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value),LEAN_SCALAR_PTR_LITERAL(59, 203, 142, 146, 93, 76, 229, 9)}};
static const lean_object* l_Lean_Parser_Module_module_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Module_module_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value),((lean_object*)&l_Lean_Parser_Module_module_formatter___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_module_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Module_module_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_module_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_commandParser_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_module_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Module_module_formatter___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Module_module_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_module_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_module_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_module_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_formatter___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value),LEAN_SCALAR_PTR_LITERAL(59, 203, 142, 146, 93, 76, 229, 9)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 14, 206, 143, 52, 229, 209, 241)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__3_value),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value)} };
static const lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parenthesizer"};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 239, 28, 252, 21, 233, 71, 221)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 114, 81, 186, 242, 59, 227, 110)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Module_prelude_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value),((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_prelude_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Module_prelude_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Module_prelude_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_prelude_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_prelude_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_prelude_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_prelude___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_prelude_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_prelude_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Module_prelude_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_prelude___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 6, 18, 235, 50, 88, 101, 248)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 254, 166, 235, 232, 231, 221, 239)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Module_public_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__0_value),((lean_object*)&l_Lean_Parser_Module_public___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_public_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Module_public_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Module_public_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_public_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_public_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_public_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_public___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_public_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_public_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Module_public_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_public___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 31, 175, 191, 217, 184, 6, 227)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Module_meta_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__0_value),((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_meta_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Module_meta_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Module_meta_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_meta_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_meta_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_meta_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_meta___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_meta_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_meta_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Module_meta_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_meta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 228, 64, 55, 26, 167, 248, 235)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 15, 60, 11, 40, 43, 177, 15)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Module_all_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__0_value),((lean_object*)&l_Lean_Parser_Module_all___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_all_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Module_all_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Module_all_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__0_value)} };
static const lean_object* l_Lean_Parser_Module_all_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_all_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_all_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Module_all___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_all_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_all_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Module_all_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_all___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 73, 92, 3, 207, 252, 164, 131)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 77, 255, 78, 93, 172, 67, 172)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Module_import_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__0_value),((lean_object*)&l_Lean_Parser_Module_import___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Module_import_parenthesizer___closed__0_value;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__1;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__2;
static const lean_closure_object l_Lean_Parser_Module_import_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_import___closed__5_value)} };
static const lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Module_import_parenthesizer___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__6;
static const lean_closure_object l_Lean_Parser_Module_import_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Parser_Module_import_parenthesizer___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__8;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__9;
static lean_once_cell_t l_Lean_Parser_Module_import_parenthesizer___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_import_parenthesizer___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_import___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 202, 16, 12, 219, 214, 31, 155)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Module_header_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_header___closed__0_value),((lean_object*)&l_Lean_Parser_Module_header___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Module_header_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Module_header_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ppLine_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_header_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_header_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Module_header_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Module_header_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Module_header_parenthesizer___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__6;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__7;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__8;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__9;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__10;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__11;
static lean_once_cell_t l_Lean_Parser_Module_header_parenthesizer___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_header_parenthesizer___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_header___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 253, 229, 230, 227, 57, 31, 73)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Module_module_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value),((lean_object*)&l_Lean_Parser_Module_module_formatter___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Module_module_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Module_module_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_commandParser_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Module_module_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Module_module_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Module_header_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Module_module_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Module_module_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Module_module_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Module_module_parenthesizer___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Module_module_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_module_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module_parenthesizer___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Module_moduleTk___closed__6_value),LEAN_SCALAR_PTR_LITERAL(59, 203, 142, 146, 93, 76, 229, 9)}};
static const lean_ctor_object l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 111, 56, 211, 136, 139, 180, 239)}};
static const lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0 = (const lean_object*)&l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Module_module___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__0;
static const lean_string_object l_Lean_Parser_Module_module___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Parser_Module_module___closed__1 = (const lean_object*)&l_Lean_Parser_Module_module___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Module_module___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Module_module___closed__1_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_Parser_Module_module___closed__2 = (const lean_object*)&l_Lean_Parser_Module_module___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Module_module___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__3;
static lean_once_cell_t l_Lean_Parser_Module_module___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__4;
static lean_once_cell_t l_Lean_Parser_Module_module___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__5;
static lean_once_cell_t l_Lean_Parser_Module_module___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__6;
static lean_once_cell_t l_Lean_Parser_Module_module___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__7;
static lean_once_cell_t l_Lean_Parser_Module_module___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__8;
static lean_once_cell_t l_Lean_Parser_Module_module___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Module_module___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module;
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__5(void){
_start:
{
uint8_t v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_10_ = 0;
v___x_11_ = 1;
v___x_12_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
v___x_13_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__3));
v___x_14_ = l_Lean_Parser_mkAntiquot(v___x_13_, v___x_12_, v___x_11_, v___x_10_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__6));
v___x_17_ = l_Lean_Parser_symbol(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__8(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_18_ = lean_obj_once(&l_Lean_Parser_Module_moduleTk___closed__7, &l_Lean_Parser_Module_moduleTk___closed__7_once, _init_l_Lean_Parser_Module_moduleTk___closed__7);
v___x_19_ = lean_unsigned_to_nat(1024u);
v___x_20_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
v___x_21_ = l_Lean_Parser_leadingNode(v___x_20_, v___x_19_, v___x_18_);
return v___x_21_;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__9(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_obj_once(&l_Lean_Parser_Module_moduleTk___closed__8, &l_Lean_Parser_Module_moduleTk___closed__8_once, _init_l_Lean_Parser_Module_moduleTk___closed__8);
v___x_23_ = lean_obj_once(&l_Lean_Parser_Module_moduleTk___closed__5, &l_Lean_Parser_Module_moduleTk___closed__5_once, _init_l_Lean_Parser_Module_moduleTk___closed__5);
v___x_24_ = l_Lean_Parser_withAntiquot(v___x_23_, v___x_22_);
return v___x_24_;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk___closed__10(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_obj_once(&l_Lean_Parser_Module_moduleTk___closed__9, &l_Lean_Parser_Module_moduleTk___closed__9_once, _init_l_Lean_Parser_Module_moduleTk___closed__9);
v___x_26_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
v___x_27_ = l_Lean_Parser_withCache(v___x_26_, v___x_25_);
return v___x_27_;
}
}
static lean_object* _init_l_Lean_Parser_Module_moduleTk(void){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Lean_Parser_Module_moduleTk___closed__10, &l_Lean_Parser_Module_moduleTk___closed__10_once, _init_l_Lean_Parser_Module_moduleTk___closed__10);
return v___x_28_;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__2(void){
_start:
{
uint8_t v___x_35_; uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_35_ = 0;
v___x_36_ = 1;
v___x_37_ = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
v___x_38_ = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__0));
v___x_39_ = l_Lean_Parser_mkAntiquot(v___x_38_, v___x_37_, v___x_36_, v___x_35_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__3(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__0));
v___x_41_ = l_Lean_Parser_symbol(v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__4(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_42_ = lean_obj_once(&l_Lean_Parser_Module_prelude___closed__3, &l_Lean_Parser_Module_prelude___closed__3_once, _init_l_Lean_Parser_Module_prelude___closed__3);
v___x_43_ = lean_unsigned_to_nat(1024u);
v___x_44_ = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
v___x_45_ = l_Lean_Parser_leadingNode(v___x_44_, v___x_43_, v___x_42_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__5(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Lean_Parser_Module_prelude___closed__4, &l_Lean_Parser_Module_prelude___closed__4_once, _init_l_Lean_Parser_Module_prelude___closed__4);
v___x_47_ = lean_obj_once(&l_Lean_Parser_Module_prelude___closed__2, &l_Lean_Parser_Module_prelude___closed__2_once, _init_l_Lean_Parser_Module_prelude___closed__2);
v___x_48_ = l_Lean_Parser_withAntiquot(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude___closed__6(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Lean_Parser_Module_prelude___closed__5, &l_Lean_Parser_Module_prelude___closed__5_once, _init_l_Lean_Parser_Module_prelude___closed__5);
v___x_50_ = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
v___x_51_ = l_Lean_Parser_withCache(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude(void){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_obj_once(&l_Lean_Parser_Module_prelude___closed__6, &l_Lean_Parser_Module_prelude___closed__6_once, _init_l_Lean_Parser_Module_prelude___closed__6);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__2(void){
_start:
{
uint8_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = 0;
v___x_60_ = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
v___x_61_ = ((lean_object*)(l_Lean_Parser_Module_public___closed__0));
v___x_62_ = l_Lean_Parser_mkAntiquot(v___x_61_, v___x_60_, v___x_59_, v___x_59_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__3(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l_Lean_Parser_Module_public___closed__0));
v___x_64_ = l_Lean_Parser_symbol(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__4(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = lean_obj_once(&l_Lean_Parser_Module_public___closed__3, &l_Lean_Parser_Module_public___closed__3_once, _init_l_Lean_Parser_Module_public___closed__3);
v___x_66_ = lean_unsigned_to_nat(1024u);
v___x_67_ = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
v___x_68_ = l_Lean_Parser_leadingNode(v___x_67_, v___x_66_, v___x_65_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__5(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_obj_once(&l_Lean_Parser_Module_public___closed__4, &l_Lean_Parser_Module_public___closed__4_once, _init_l_Lean_Parser_Module_public___closed__4);
v___x_70_ = lean_obj_once(&l_Lean_Parser_Module_public___closed__2, &l_Lean_Parser_Module_public___closed__2_once, _init_l_Lean_Parser_Module_public___closed__2);
v___x_71_ = l_Lean_Parser_withAntiquot(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_Parser_Module_public___closed__6(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_obj_once(&l_Lean_Parser_Module_public___closed__5, &l_Lean_Parser_Module_public___closed__5_once, _init_l_Lean_Parser_Module_public___closed__5);
v___x_73_ = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
v___x_74_ = l_Lean_Parser_withCache(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Parser_Module_public(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_once(&l_Lean_Parser_Module_public___closed__6, &l_Lean_Parser_Module_public___closed__6_once, _init_l_Lean_Parser_Module_public___closed__6);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__2(void){
_start:
{
uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = 0;
v___x_83_ = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
v___x_84_ = ((lean_object*)(l_Lean_Parser_Module_meta___closed__0));
v___x_85_ = l_Lean_Parser_mkAntiquot(v___x_84_, v___x_83_, v___x_82_, v___x_82_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__3(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(l_Lean_Parser_Module_meta___closed__0));
v___x_87_ = l_Lean_Parser_symbol(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__4(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = lean_obj_once(&l_Lean_Parser_Module_meta___closed__3, &l_Lean_Parser_Module_meta___closed__3_once, _init_l_Lean_Parser_Module_meta___closed__3);
v___x_89_ = lean_unsigned_to_nat(1024u);
v___x_90_ = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
v___x_91_ = l_Lean_Parser_leadingNode(v___x_90_, v___x_89_, v___x_88_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__5(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_obj_once(&l_Lean_Parser_Module_meta___closed__4, &l_Lean_Parser_Module_meta___closed__4_once, _init_l_Lean_Parser_Module_meta___closed__4);
v___x_93_ = lean_obj_once(&l_Lean_Parser_Module_meta___closed__2, &l_Lean_Parser_Module_meta___closed__2_once, _init_l_Lean_Parser_Module_meta___closed__2);
v___x_94_ = l_Lean_Parser_withAntiquot(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta___closed__6(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l_Lean_Parser_Module_meta___closed__5, &l_Lean_Parser_Module_meta___closed__5_once, _init_l_Lean_Parser_Module_meta___closed__5);
v___x_96_ = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
v___x_97_ = l_Lean_Parser_withCache(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Parser_Module_meta(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Lean_Parser_Module_meta___closed__6, &l_Lean_Parser_Module_meta___closed__6_once, _init_l_Lean_Parser_Module_meta___closed__6);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__2(void){
_start:
{
uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = 0;
v___x_106_ = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
v___x_107_ = ((lean_object*)(l_Lean_Parser_Module_all___closed__0));
v___x_108_ = l_Lean_Parser_mkAntiquot(v___x_107_, v___x_106_, v___x_105_, v___x_105_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__3(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_Parser_Module_all___closed__0));
v___x_110_ = l_Lean_Parser_symbol(v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__4(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_111_ = lean_obj_once(&l_Lean_Parser_Module_all___closed__3, &l_Lean_Parser_Module_all___closed__3_once, _init_l_Lean_Parser_Module_all___closed__3);
v___x_112_ = lean_unsigned_to_nat(1024u);
v___x_113_ = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
v___x_114_ = l_Lean_Parser_leadingNode(v___x_113_, v___x_112_, v___x_111_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__5(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_obj_once(&l_Lean_Parser_Module_all___closed__4, &l_Lean_Parser_Module_all___closed__4_once, _init_l_Lean_Parser_Module_all___closed__4);
v___x_116_ = lean_obj_once(&l_Lean_Parser_Module_all___closed__2, &l_Lean_Parser_Module_all___closed__2_once, _init_l_Lean_Parser_Module_all___closed__2);
v___x_117_ = l_Lean_Parser_withAntiquot(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Parser_Module_all___closed__6(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_obj_once(&l_Lean_Parser_Module_all___closed__5, &l_Lean_Parser_Module_all___closed__5_once, _init_l_Lean_Parser_Module_all___closed__5);
v___x_119_ = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
v___x_120_ = l_Lean_Parser_withCache(v___x_119_, v___x_118_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Parser_Module_all(void){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_obj_once(&l_Lean_Parser_Module_all___closed__6, &l_Lean_Parser_Module_all___closed__6_once, _init_l_Lean_Parser_Module_all___closed__6);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__2(void){
_start:
{
uint8_t v___x_128_; uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_128_ = 0;
v___x_129_ = 1;
v___x_130_ = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
v___x_131_ = ((lean_object*)(l_Lean_Parser_Module_import___closed__0));
v___x_132_ = l_Lean_Parser_mkAntiquot(v___x_131_, v___x_130_, v___x_129_, v___x_128_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__3(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = l_Lean_Parser_Module_public;
v___x_134_ = l_Lean_Parser_optional(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__4(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = l_Lean_Parser_Module_meta;
v___x_136_ = l_Lean_Parser_optional(v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__6(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(l_Lean_Parser_Module_import___closed__5));
v___x_139_ = l_Lean_Parser_symbol(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__7(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_obj_once(&l_Lean_Parser_Module_import___closed__6, &l_Lean_Parser_Module_import___closed__6_once, _init_l_Lean_Parser_Module_import___closed__6);
v___x_141_ = lean_obj_once(&l_Lean_Parser_Module_import___closed__4, &l_Lean_Parser_Module_import___closed__4_once, _init_l_Lean_Parser_Module_import___closed__4);
v___x_142_ = l_Lean_Parser_andthen(v___x_141_, v___x_140_);
return v___x_142_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__8(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_obj_once(&l_Lean_Parser_Module_import___closed__7, &l_Lean_Parser_Module_import___closed__7_once, _init_l_Lean_Parser_Module_import___closed__7);
v___x_144_ = lean_obj_once(&l_Lean_Parser_Module_import___closed__3, &l_Lean_Parser_Module_import___closed__3_once, _init_l_Lean_Parser_Module_import___closed__3);
v___x_145_ = l_Lean_Parser_andthen(v___x_144_, v___x_143_);
return v___x_145_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__9(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_obj_once(&l_Lean_Parser_Module_import___closed__8, &l_Lean_Parser_Module_import___closed__8_once, _init_l_Lean_Parser_Module_import___closed__8);
v___x_147_ = l_Lean_Parser_atomic(v___x_146_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__10(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = l_Lean_Parser_Module_all;
v___x_149_ = l_Lean_Parser_optional(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__11(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = l_Lean_Parser_identWithPartialTrailingDot;
v___x_151_ = lean_obj_once(&l_Lean_Parser_Module_import___closed__10, &l_Lean_Parser_Module_import___closed__10_once, _init_l_Lean_Parser_Module_import___closed__10);
v___x_152_ = l_Lean_Parser_andthen(v___x_151_, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__12(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = lean_obj_once(&l_Lean_Parser_Module_import___closed__11, &l_Lean_Parser_Module_import___closed__11_once, _init_l_Lean_Parser_Module_import___closed__11);
v___x_154_ = lean_obj_once(&l_Lean_Parser_Module_import___closed__9, &l_Lean_Parser_Module_import___closed__9_once, _init_l_Lean_Parser_Module_import___closed__9);
v___x_155_ = l_Lean_Parser_andthen(v___x_154_, v___x_153_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__13(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = lean_obj_once(&l_Lean_Parser_Module_import___closed__12, &l_Lean_Parser_Module_import___closed__12_once, _init_l_Lean_Parser_Module_import___closed__12);
v___x_157_ = lean_unsigned_to_nat(1024u);
v___x_158_ = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
v___x_159_ = l_Lean_Parser_leadingNode(v___x_158_, v___x_157_, v___x_156_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__14(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_obj_once(&l_Lean_Parser_Module_import___closed__13, &l_Lean_Parser_Module_import___closed__13_once, _init_l_Lean_Parser_Module_import___closed__13);
v___x_161_ = lean_obj_once(&l_Lean_Parser_Module_import___closed__2, &l_Lean_Parser_Module_import___closed__2_once, _init_l_Lean_Parser_Module_import___closed__2);
v___x_162_ = l_Lean_Parser_withAntiquot(v___x_161_, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import___closed__15(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_obj_once(&l_Lean_Parser_Module_import___closed__14, &l_Lean_Parser_Module_import___closed__14_once, _init_l_Lean_Parser_Module_import___closed__14);
v___x_164_ = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
v___x_165_ = l_Lean_Parser_withCache(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&l_Lean_Parser_Module_import___closed__15, &l_Lean_Parser_Module_import___closed__15_once, _init_l_Lean_Parser_Module_import___closed__15);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__2(void){
_start:
{
uint8_t v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_173_ = 0;
v___x_174_ = 1;
v___x_175_ = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
v___x_176_ = ((lean_object*)(l_Lean_Parser_Module_header___closed__0));
v___x_177_ = l_Lean_Parser_mkAntiquot(v___x_176_, v___x_175_, v___x_174_, v___x_173_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__3(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = l_Lean_Parser_skip;
v___x_179_ = l_Lean_Parser_andthen(v___x_178_, v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__4(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__3, &l_Lean_Parser_Module_header___closed__3_once, _init_l_Lean_Parser_Module_header___closed__3);
v___x_181_ = l_Lean_Parser_Module_moduleTk;
v___x_182_ = l_Lean_Parser_andthen(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__5(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__4, &l_Lean_Parser_Module_header___closed__4_once, _init_l_Lean_Parser_Module_header___closed__4);
v___x_184_ = l_Lean_Parser_optional(v___x_183_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__6(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = l_Lean_Parser_skip;
v___x_186_ = l_Lean_Parser_Module_prelude;
v___x_187_ = l_Lean_Parser_andthen(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__7(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__6, &l_Lean_Parser_Module_header___closed__6_once, _init_l_Lean_Parser_Module_header___closed__6);
v___x_189_ = l_Lean_Parser_optional(v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__8(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = l_Lean_Parser_skip;
v___x_191_ = l_Lean_Parser_Module_import;
v___x_192_ = l_Lean_Parser_andthen(v___x_191_, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__9(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__8, &l_Lean_Parser_Module_header___closed__8_once, _init_l_Lean_Parser_Module_header___closed__8);
v___x_194_ = l_Lean_Parser_many(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__10(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = l_Lean_Parser_skip;
v___x_196_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__9, &l_Lean_Parser_Module_header___closed__9_once, _init_l_Lean_Parser_Module_header___closed__9);
v___x_197_ = l_Lean_Parser_andthen(v___x_196_, v___x_195_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__11(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__10, &l_Lean_Parser_Module_header___closed__10_once, _init_l_Lean_Parser_Module_header___closed__10);
v___x_199_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__7, &l_Lean_Parser_Module_header___closed__7_once, _init_l_Lean_Parser_Module_header___closed__7);
v___x_200_ = l_Lean_Parser_andthen(v___x_199_, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__12(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__11, &l_Lean_Parser_Module_header___closed__11_once, _init_l_Lean_Parser_Module_header___closed__11);
v___x_202_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__5, &l_Lean_Parser_Module_header___closed__5_once, _init_l_Lean_Parser_Module_header___closed__5);
v___x_203_ = l_Lean_Parser_andthen(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__13(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_204_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__12, &l_Lean_Parser_Module_header___closed__12_once, _init_l_Lean_Parser_Module_header___closed__12);
v___x_205_ = lean_unsigned_to_nat(1024u);
v___x_206_ = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
v___x_207_ = l_Lean_Parser_leadingNode(v___x_206_, v___x_205_, v___x_204_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__14(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__13, &l_Lean_Parser_Module_header___closed__13_once, _init_l_Lean_Parser_Module_header___closed__13);
v___x_209_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__2, &l_Lean_Parser_Module_header___closed__2_once, _init_l_Lean_Parser_Module_header___closed__2);
v___x_210_ = l_Lean_Parser_withAntiquot(v___x_209_, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header___closed__15(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__14, &l_Lean_Parser_Module_header___closed__14_once, _init_l_Lean_Parser_Module_header___closed__14);
v___x_212_ = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
v___x_213_ = l_Lean_Parser_withCache(v___x_212_, v___x_211_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header(void){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__15, &l_Lean_Parser_Module_header___closed__15_once, _init_l_Lean_Parser_Module_header___closed__15);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_formatter(lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk_formatter___closed__0));
v___x_234_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk_formatter___closed__2));
v___x_235_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_233_, v___x_234_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_formatter___boxed(lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Parser_Module_moduleTk_formatter(v_a_236_, v_a_237_, v_a_238_, v_a_239_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3(){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_250_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_251_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
v___x_252_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1));
v___x_253_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_formatter___boxed), 5, 0);
v___x_254_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_250_, v___x_251_, v___x_252_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___boxed(lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3();
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_formatter(lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = ((lean_object*)(l_Lean_Parser_Module_prelude_formatter___closed__0));
v___x_276_ = ((lean_object*)(l_Lean_Parser_Module_prelude_formatter___closed__2));
v___x_277_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_275_, v___x_276_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_formatter___boxed(lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Parser_Module_prelude_formatter(v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7(){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_291_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_292_ = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
v___x_293_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0));
v___x_294_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_formatter___boxed), 5, 0);
v___x_295_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_291_, v___x_292_, v___x_293_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___boxed(lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7();
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_formatter(lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = ((lean_object*)(l_Lean_Parser_Module_public_formatter___closed__0));
v___x_316_ = ((lean_object*)(l_Lean_Parser_Module_public_formatter___closed__2));
v___x_317_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_315_, v___x_316_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_formatter___boxed(lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Parser_Module_public_formatter(v_a_318_, v_a_319_, v_a_320_, v_a_321_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11(){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_331_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_332_ = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
v___x_333_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0));
v___x_334_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_formatter___boxed), 5, 0);
v___x_335_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_331_, v___x_332_, v___x_333_, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___boxed(lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11();
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_formatter(lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = ((lean_object*)(l_Lean_Parser_Module_meta_formatter___closed__0));
v___x_356_ = ((lean_object*)(l_Lean_Parser_Module_meta_formatter___closed__2));
v___x_357_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_355_, v___x_356_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_formatter___boxed(lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Parser_Module_meta_formatter(v_a_358_, v_a_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15(){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_371_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_372_ = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
v___x_373_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0));
v___x_374_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_formatter___boxed), 5, 0);
v___x_375_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_371_, v___x_372_, v___x_373_, v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___boxed(lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15();
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_formatter(lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = ((lean_object*)(l_Lean_Parser_Module_all_formatter___closed__0));
v___x_396_ = ((lean_object*)(l_Lean_Parser_Module_all_formatter___closed__2));
v___x_397_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_395_, v___x_396_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_formatter___boxed(lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Parser_Module_all_formatter(v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19(){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_411_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_412_ = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
v___x_413_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0));
v___x_414_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_formatter___boxed), 5, 0);
v___x_415_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_411_, v___x_412_, v___x_413_, v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___boxed(lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19();
return v_res_417_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__1(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_formatter___boxed), 5, 0);
v___x_426_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__2(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_formatter___boxed), 5, 0);
v___x_428_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__4(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = ((lean_object*)(l_Lean_Parser_Module_import_formatter___closed__3));
v___x_432_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__2, &l_Lean_Parser_Module_import_formatter___closed__2_once, _init_l_Lean_Parser_Module_import_formatter___closed__2);
v___x_433_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_433_, 0, v___x_432_);
lean_closure_set(v___x_433_, 1, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__5(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__4, &l_Lean_Parser_Module_import_formatter___closed__4_once, _init_l_Lean_Parser_Module_import_formatter___closed__4);
v___x_435_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__1, &l_Lean_Parser_Module_import_formatter___closed__1_once, _init_l_Lean_Parser_Module_import_formatter___closed__1);
v___x_436_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_436_, 0, v___x_435_);
lean_closure_set(v___x_436_, 1, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__6(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__5, &l_Lean_Parser_Module_import_formatter___closed__5_once, _init_l_Lean_Parser_Module_import_formatter___closed__5);
v___x_438_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__7(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_formatter___boxed), 5, 0);
v___x_440_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__9(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = ((lean_object*)(l_Lean_Parser_Module_import_formatter___closed__8));
v___x_443_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__7, &l_Lean_Parser_Module_import_formatter___closed__7_once, _init_l_Lean_Parser_Module_import_formatter___closed__7);
v___x_444_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_444_, 0, v___x_443_);
lean_closure_set(v___x_444_, 1, v___x_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__10(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__9, &l_Lean_Parser_Module_import_formatter___closed__9_once, _init_l_Lean_Parser_Module_import_formatter___closed__9);
v___x_446_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__6, &l_Lean_Parser_Module_import_formatter___closed__6_once, _init_l_Lean_Parser_Module_import_formatter___closed__6);
v___x_447_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_447_, 0, v___x_446_);
lean_closure_set(v___x_447_, 1, v___x_445_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__11(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_448_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__10, &l_Lean_Parser_Module_import_formatter___closed__10_once, _init_l_Lean_Parser_Module_import_formatter___closed__10);
v___x_449_ = lean_unsigned_to_nat(1024u);
v___x_450_ = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
v___x_451_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_451_, 0, v___x_450_);
lean_closure_set(v___x_451_, 1, v___x_449_);
lean_closure_set(v___x_451_, 2, v___x_448_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_formatter(lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = ((lean_object*)(l_Lean_Parser_Module_import_formatter___closed__0));
v___x_458_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__11, &l_Lean_Parser_Module_import_formatter___closed__11_once, _init_l_Lean_Parser_Module_import_formatter___closed__11);
v___x_459_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_457_, v___x_458_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_formatter___boxed(lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Parser_Module_import_formatter(v_a_460_, v_a_461_, v_a_462_, v_a_463_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23(){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_473_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_474_ = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
v___x_475_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0));
v___x_476_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_formatter___boxed), 5, 0);
v___x_477_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_473_, v___x_474_, v___x_475_, v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___boxed(lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23();
return v_res_479_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__1(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
lean_inc_ref(v___x_487_);
v___x_488_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_488_, 0, v___x_487_);
lean_closure_set(v___x_488_, 1, v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__2(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__1, &l_Lean_Parser_Module_header_formatter___closed__1_once, _init_l_Lean_Parser_Module_header_formatter___closed__1);
v___x_490_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_formatter___boxed), 5, 0);
v___x_491_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_491_, 0, v___x_490_);
lean_closure_set(v___x_491_, 1, v___x_489_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__3(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__2, &l_Lean_Parser_Module_header_formatter___closed__2_once, _init_l_Lean_Parser_Module_header_formatter___closed__2);
v___x_493_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__4(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
v___x_495_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_formatter___boxed), 5, 0);
v___x_496_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_496_, 0, v___x_495_);
lean_closure_set(v___x_496_, 1, v___x_494_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__5(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__4, &l_Lean_Parser_Module_header_formatter___closed__4_once, _init_l_Lean_Parser_Module_header_formatter___closed__4);
v___x_498_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__6(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
v___x_500_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_formatter___boxed), 5, 0);
v___x_501_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_501_, 0, v___x_500_);
lean_closure_set(v___x_501_, 1, v___x_499_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__7(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__6, &l_Lean_Parser_Module_header_formatter___closed__6_once, _init_l_Lean_Parser_Module_header_formatter___closed__6);
v___x_503_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__8(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
v___x_505_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__7, &l_Lean_Parser_Module_header_formatter___closed__7_once, _init_l_Lean_Parser_Module_header_formatter___closed__7);
v___x_506_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_506_, 0, v___x_505_);
lean_closure_set(v___x_506_, 1, v___x_504_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__9(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__8, &l_Lean_Parser_Module_header_formatter___closed__8_once, _init_l_Lean_Parser_Module_header_formatter___closed__8);
v___x_508_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__5, &l_Lean_Parser_Module_header_formatter___closed__5_once, _init_l_Lean_Parser_Module_header_formatter___closed__5);
v___x_509_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_509_, 0, v___x_508_);
lean_closure_set(v___x_509_, 1, v___x_507_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__10(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__9, &l_Lean_Parser_Module_header_formatter___closed__9_once, _init_l_Lean_Parser_Module_header_formatter___closed__9);
v___x_511_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__3, &l_Lean_Parser_Module_header_formatter___closed__3_once, _init_l_Lean_Parser_Module_header_formatter___closed__3);
v___x_512_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_512_, 0, v___x_511_);
lean_closure_set(v___x_512_, 1, v___x_510_);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__11(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__10, &l_Lean_Parser_Module_header_formatter___closed__10_once, _init_l_Lean_Parser_Module_header_formatter___closed__10);
v___x_514_ = lean_unsigned_to_nat(1024u);
v___x_515_ = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
v___x_516_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_516_, 0, v___x_515_);
lean_closure_set(v___x_516_, 1, v___x_514_);
lean_closure_set(v___x_516_, 2, v___x_513_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_formatter(lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = ((lean_object*)(l_Lean_Parser_Module_header_formatter___closed__0));
v___x_523_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__11, &l_Lean_Parser_Module_header_formatter___closed__11_once, _init_l_Lean_Parser_Module_header_formatter___closed__11);
v___x_524_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_522_, v___x_523_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_formatter___boxed(lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Parser_Module_header_formatter(v_a_525_, v_a_526_, v_a_527_, v_a_528_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27(){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_538_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_539_ = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
v___x_540_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0));
v___x_541_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_formatter___boxed), 5, 0);
v___x_542_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_538_, v___x_539_, v___x_540_, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___boxed(lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27();
return v_res_544_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__3(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__1, &l_Lean_Parser_Module_header_formatter___closed__1_once, _init_l_Lean_Parser_Module_header_formatter___closed__1);
v___x_560_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__2));
v___x_561_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_561_, 0, v___x_560_);
lean_closure_set(v___x_561_, 1, v___x_559_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__4(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_obj_once(&l_Lean_Parser_Module_module_formatter___closed__3, &l_Lean_Parser_Module_module_formatter___closed__3_once, _init_l_Lean_Parser_Module_module_formatter___closed__3);
v___x_563_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__5(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = lean_obj_once(&l_Lean_Parser_Module_module_formatter___closed__4, &l_Lean_Parser_Module_module_formatter___closed__4_once, _init_l_Lean_Parser_Module_module_formatter___closed__4);
v___x_565_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_formatter___boxed), 5, 0);
v___x_566_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_566_, 0, v___x_565_);
lean_closure_set(v___x_566_, 1, v___x_564_);
return v___x_566_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__6(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = lean_obj_once(&l_Lean_Parser_Module_module_formatter___closed__5, &l_Lean_Parser_Module_module_formatter___closed__5_once, _init_l_Lean_Parser_Module_module_formatter___closed__5);
v___x_568_ = lean_unsigned_to_nat(1024u);
v___x_569_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_570_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_570_, 0, v___x_569_);
lean_closure_set(v___x_570_, 1, v___x_568_);
lean_closure_set(v___x_570_, 2, v___x_567_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_formatter(lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__1));
v___x_577_ = lean_obj_once(&l_Lean_Parser_Module_module_formatter___closed__6, &l_Lean_Parser_Module_module_formatter___closed__6_once, _init_l_Lean_Parser_Module_module_formatter___closed__6);
v___x_578_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_576_, v___x_577_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_formatter___boxed(lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Parser_Module_module_formatter(v_a_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31(){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_592_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_593_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_594_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0));
v___x_595_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_formatter___boxed), 5, 0);
v___x_596_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_592_, v___x_593_, v___x_594_, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___boxed(lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31();
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer(lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0));
v___x_618_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2));
v___x_619_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_617_, v___x_618_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer___boxed(lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_Parser_Module_moduleTk_parenthesizer(v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35(){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_634_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_635_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
v___x_636_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1));
v___x_637_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_parenthesizer___boxed), 5, 0);
v___x_638_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_634_, v___x_635_, v___x_636_, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___boxed(lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35();
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_parenthesizer(lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = ((lean_object*)(l_Lean_Parser_Module_prelude_parenthesizer___closed__0));
v___x_660_ = ((lean_object*)(l_Lean_Parser_Module_prelude_parenthesizer___closed__2));
v___x_661_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_659_, v___x_660_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_parenthesizer___boxed(lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Parser_Module_prelude_parenthesizer(v_a_662_, v_a_663_, v_a_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39(){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_675_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_676_ = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
v___x_677_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0));
v___x_678_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_parenthesizer___boxed), 5, 0);
v___x_679_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_675_, v___x_676_, v___x_677_, v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___boxed(lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39();
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_parenthesizer(lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((lean_object*)(l_Lean_Parser_Module_public_parenthesizer___closed__0));
v___x_700_ = ((lean_object*)(l_Lean_Parser_Module_public_parenthesizer___closed__2));
v___x_701_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_699_, v___x_700_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_parenthesizer___boxed(lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Parser_Module_public_parenthesizer(v_a_702_, v_a_703_, v_a_704_, v_a_705_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43(){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_715_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_716_ = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
v___x_717_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0));
v___x_718_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_parenthesizer___boxed), 5, 0);
v___x_719_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_715_, v___x_716_, v___x_717_, v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___boxed(lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43();
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_parenthesizer(lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = ((lean_object*)(l_Lean_Parser_Module_meta_parenthesizer___closed__0));
v___x_740_ = ((lean_object*)(l_Lean_Parser_Module_meta_parenthesizer___closed__2));
v___x_741_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_739_, v___x_740_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_parenthesizer___boxed(lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Parser_Module_meta_parenthesizer(v_a_742_, v_a_743_, v_a_744_, v_a_745_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47(){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_755_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_756_ = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
v___x_757_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0));
v___x_758_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_parenthesizer___boxed), 5, 0);
v___x_759_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_755_, v___x_756_, v___x_757_, v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___boxed(lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47();
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_parenthesizer(lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = ((lean_object*)(l_Lean_Parser_Module_all_parenthesizer___closed__0));
v___x_780_ = ((lean_object*)(l_Lean_Parser_Module_all_parenthesizer___closed__2));
v___x_781_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_779_, v___x_780_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_parenthesizer___boxed(lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Parser_Module_all_parenthesizer(v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51(){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_795_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_796_ = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
v___x_797_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0));
v___x_798_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_parenthesizer___boxed), 5, 0);
v___x_799_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_795_, v___x_796_, v___x_797_, v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___boxed(lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51();
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___lam__0(lean_object* v___x_802_, lean_object* v___x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_802_, v___x_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___lam__0___boxed(lean_object* v___x_810_, lean_object* v___x_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_Parser_Module_import_parenthesizer___lam__0(v___x_810_, v___x_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
return v_res_817_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_parenthesizer___boxed), 5, 0);
v___x_826_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_parenthesizer___boxed), 5, 0);
v___x_828_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = ((lean_object*)(l_Lean_Parser_Module_import_parenthesizer___closed__3));
v___x_832_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__2, &l_Lean_Parser_Module_import_parenthesizer___closed__2_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__2);
v___x_833_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_833_, 0, v___x_832_);
lean_closure_set(v___x_833_, 1, v___x_831_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___f_836_; 
v___x_834_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__4, &l_Lean_Parser_Module_import_parenthesizer___closed__4_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__4);
v___x_835_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__1, &l_Lean_Parser_Module_import_parenthesizer___closed__1_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__1);
v___f_836_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_836_, 0, v___x_835_);
lean_closure_set(v___f_836_, 1, v___x_834_);
return v___f_836_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_parenthesizer___boxed), 5, 0);
v___x_838_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = ((lean_object*)(l_Lean_Parser_Module_import_parenthesizer___closed__7));
v___x_841_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__6, &l_Lean_Parser_Module_import_parenthesizer___closed__6_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__6);
v___x_842_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_842_, 0, v___x_841_);
lean_closure_set(v___x_842_, 1, v___x_840_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_843_; lean_object* v___f_844_; lean_object* v___x_845_; 
v___x_843_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__8, &l_Lean_Parser_Module_import_parenthesizer___closed__8_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__8);
v___f_844_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__5, &l_Lean_Parser_Module_import_parenthesizer___closed__5_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__5);
v___x_845_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_845_, 0, v___f_844_);
lean_closure_set(v___x_845_, 1, v___x_843_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_846_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__9, &l_Lean_Parser_Module_import_parenthesizer___closed__9_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__9);
v___x_847_ = lean_unsigned_to_nat(1024u);
v___x_848_ = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
v___x_849_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_849_, 0, v___x_848_);
lean_closure_set(v___x_849_, 1, v___x_847_);
lean_closure_set(v___x_849_, 2, v___x_846_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer(lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = ((lean_object*)(l_Lean_Parser_Module_import_parenthesizer___closed__0));
v___x_856_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__10, &l_Lean_Parser_Module_import_parenthesizer___closed__10_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__10);
v___x_857_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_855_, v___x_856_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___boxed(lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_Parser_Module_import_parenthesizer(v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55(){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_871_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_872_ = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
v___x_873_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0));
v___x_874_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer___boxed), 5, 0);
v___x_875_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_871_, v___x_872_, v___x_873_, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___boxed(lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55();
return v_res_877_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__2));
v___x_889_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_parenthesizer___boxed), 5, 0);
v___x_890_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_890_, 0, v___x_889_);
lean_closure_set(v___x_890_, 1, v___x_888_);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__3, &l_Lean_Parser_Module_header_parenthesizer___closed__3_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__3);
v___x_892_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__1));
v___x_894_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_parenthesizer___boxed), 5, 0);
v___x_895_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_895_, 0, v___x_894_);
lean_closure_set(v___x_895_, 1, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__5, &l_Lean_Parser_Module_header_parenthesizer___closed__5_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__5);
v___x_897_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__1));
v___x_899_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer___boxed), 5, 0);
v___x_900_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_900_, 0, v___x_899_);
lean_closure_set(v___x_900_, 1, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__7, &l_Lean_Parser_Module_header_parenthesizer___closed__7_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__7);
v___x_902_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__1));
v___x_904_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__8, &l_Lean_Parser_Module_header_parenthesizer___closed__8_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__8);
v___x_905_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_905_, 0, v___x_904_);
lean_closure_set(v___x_905_, 1, v___x_903_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__9, &l_Lean_Parser_Module_header_parenthesizer___closed__9_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__9);
v___x_907_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__6, &l_Lean_Parser_Module_header_parenthesizer___closed__6_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__6);
v___x_908_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_908_, 0, v___x_907_);
lean_closure_set(v___x_908_, 1, v___x_906_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__10, &l_Lean_Parser_Module_header_parenthesizer___closed__10_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__10);
v___x_910_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__4, &l_Lean_Parser_Module_header_parenthesizer___closed__4_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__4);
v___x_911_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_911_, 0, v___x_910_);
lean_closure_set(v___x_911_, 1, v___x_909_);
return v___x_911_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__12(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_912_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__11, &l_Lean_Parser_Module_header_parenthesizer___closed__11_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__11);
v___x_913_ = lean_unsigned_to_nat(1024u);
v___x_914_ = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
v___x_915_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_915_, 0, v___x_914_);
lean_closure_set(v___x_915_, 1, v___x_913_);
lean_closure_set(v___x_915_, 2, v___x_912_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer(lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__0));
v___x_922_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__12, &l_Lean_Parser_Module_header_parenthesizer___closed__12_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__12);
v___x_923_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_921_, v___x_922_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer___boxed(lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_Parser_Module_header_parenthesizer(v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59(){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_937_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_938_ = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
v___x_939_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0));
v___x_940_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_parenthesizer___boxed), 5, 0);
v___x_941_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_937_, v___x_938_, v___x_939_, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___boxed(lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59();
return v_res_943_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = ((lean_object*)(l_Lean_Parser_Module_module_parenthesizer___closed__3));
v___x_959_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_parenthesizer___boxed), 5, 0);
v___x_960_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_960_, 0, v___x_959_);
lean_closure_set(v___x_960_, 1, v___x_958_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_961_ = lean_obj_once(&l_Lean_Parser_Module_module_parenthesizer___closed__4, &l_Lean_Parser_Module_module_parenthesizer___closed__4_once, _init_l_Lean_Parser_Module_module_parenthesizer___closed__4);
v___x_962_ = lean_unsigned_to_nat(1024u);
v___x_963_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_964_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_964_, 0, v___x_963_);
lean_closure_set(v___x_964_, 1, v___x_962_);
lean_closure_set(v___x_964_, 2, v___x_961_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_parenthesizer(lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_970_ = ((lean_object*)(l_Lean_Parser_Module_module_parenthesizer___closed__0));
v___x_971_ = lean_obj_once(&l_Lean_Parser_Module_module_parenthesizer___closed__5, &l_Lean_Parser_Module_module_parenthesizer___closed__5_once, _init_l_Lean_Parser_Module_module_parenthesizer___closed__5);
v___x_972_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_970_, v___x_971_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_parenthesizer___boxed(lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Parser_Module_module_parenthesizer(v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63(){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_986_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_987_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_988_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0));
v___x_989_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_parenthesizer___boxed), 5, 0);
v___x_990_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_986_, v___x_987_, v___x_988_, v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___boxed(lean_object* v_a_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63();
return v_res_992_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__0(void){
_start:
{
uint8_t v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_993_ = 0;
v___x_994_ = 1;
v___x_995_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_996_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__6));
v___x_997_ = l_Lean_Parser_mkAntiquot(v___x_996_, v___x_995_, v___x_994_, v___x_993_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__3(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = lean_unsigned_to_nat(0u);
v___x_1002_ = ((lean_object*)(l_Lean_Parser_Module_module___closed__2));
v___x_1003_ = l_Lean_Parser_categoryParser(v___x_1002_, v___x_1001_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__4(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__3, &l_Lean_Parser_Module_header___closed__3_once, _init_l_Lean_Parser_Module_header___closed__3);
v___x_1005_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__3, &l_Lean_Parser_Module_module___closed__3_once, _init_l_Lean_Parser_Module_module___closed__3);
v___x_1006_ = l_Lean_Parser_andthen(v___x_1005_, v___x_1004_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__5(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__4, &l_Lean_Parser_Module_module___closed__4_once, _init_l_Lean_Parser_Module_module___closed__4);
v___x_1008_ = l_Lean_Parser_many(v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__6(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__5, &l_Lean_Parser_Module_module___closed__5_once, _init_l_Lean_Parser_Module_module___closed__5);
v___x_1010_ = l_Lean_Parser_Module_header;
v___x_1011_ = l_Lean_Parser_andthen(v___x_1010_, v___x_1009_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__7(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1012_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__6, &l_Lean_Parser_Module_module___closed__6_once, _init_l_Lean_Parser_Module_module___closed__6);
v___x_1013_ = lean_unsigned_to_nat(1024u);
v___x_1014_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_1015_ = l_Lean_Parser_leadingNode(v___x_1014_, v___x_1013_, v___x_1012_);
return v___x_1015_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__8(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__7, &l_Lean_Parser_Module_module___closed__7_once, _init_l_Lean_Parser_Module_module___closed__7);
v___x_1017_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__0, &l_Lean_Parser_Module_module___closed__0_once, _init_l_Lean_Parser_Module_module___closed__0);
v___x_1018_ = l_Lean_Parser_withAntiquot(v___x_1017_, v___x_1016_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__9(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__8, &l_Lean_Parser_Module_module___closed__8_once, _init_l_Lean_Parser_Module_module___closed__8);
v___x_1020_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_1021_ = l_Lean_Parser_withCache(v___x_1020_, v___x_1019_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module(void){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__9, &l_Lean_Parser_Module_module___closed__9_once, _init_l_Lean_Parser_Module_module___closed__9);
return v___x_1022_;
}
}
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Module_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_moduleTk = _init_l_Lean_Parser_Module_moduleTk();
lean_mark_persistent(l_Lean_Parser_Module_moduleTk);
l_Lean_Parser_Module_prelude = _init_l_Lean_Parser_Module_prelude();
lean_mark_persistent(l_Lean_Parser_Module_prelude);
l_Lean_Parser_Module_public = _init_l_Lean_Parser_Module_public();
lean_mark_persistent(l_Lean_Parser_Module_public);
l_Lean_Parser_Module_meta = _init_l_Lean_Parser_Module_meta();
lean_mark_persistent(l_Lean_Parser_Module_meta);
l_Lean_Parser_Module_all = _init_l_Lean_Parser_Module_all();
lean_mark_persistent(l_Lean_Parser_Module_all);
l_Lean_Parser_Module_import = _init_l_Lean_Parser_Module_import();
lean_mark_persistent(l_Lean_Parser_Module_import);
l_Lean_Parser_Module_header = _init_l_Lean_Parser_Module_header();
lean_mark_persistent(l_Lean_Parser_Module_header);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_module = _init_l_Lean_Parser_Module_module();
lean_mark_persistent(l_Lean_Parser_Module_module);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Module_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Module_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Module_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Module_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Module_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
