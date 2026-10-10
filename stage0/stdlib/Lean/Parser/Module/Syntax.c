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
lean_object* l_Lean_Parser_Module_moduleTk_formatter(lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk_formatter___closed__0));
v___x_234_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk_formatter___closed__2));
v___x_235_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_233_, v___x_234_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
return v___x_235_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_moduleTk_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_228_ = stack[0].m_obj;
lean_object* v_a_229_ = stack[1].m_obj;
lean_object* v_a_230_ = stack[2].m_obj;
lean_object* v_a_231_ = stack[3].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Lean_Parser_Module_moduleTk_formatter(v_a_228_, v_a_229_, v_a_230_, v_a_231_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_formatter___boxed(lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_Parser_Module_moduleTk_formatter(v_a_237_, v_a_238_, v_a_239_, v_a_240_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
return v_res_242_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3(){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_251_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_252_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
v___x_253_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___closed__1));
v___x_254_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_formatter___boxed), 5, 0);
v___x_255_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_251_, v___x_252_, v___x_253_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_256_;
v_res_256_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3();
stack->m_obj
 = v_res_256_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3___boxed(lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_formatter__3();
return v_res_258_;
}
}
lean_object* l_Lean_Parser_Module_prelude_formatter(lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = ((lean_object*)(l_Lean_Parser_Module_prelude_formatter___closed__0));
v___x_278_ = ((lean_object*)(l_Lean_Parser_Module_prelude_formatter___closed__2));
v___x_279_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_277_, v___x_278_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
return v___x_279_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_prelude_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_272_ = stack[0].m_obj;
lean_object* v_a_273_ = stack[1].m_obj;
lean_object* v_a_274_ = stack[2].m_obj;
lean_object* v_a_275_ = stack[3].m_obj;
lean_object* v_res_280_;
v_res_280_ = l_Lean_Parser_Module_prelude_formatter(v_a_272_, v_a_273_, v_a_274_, v_a_275_);
stack->m_obj
 = v_res_280_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_formatter___boxed(lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Parser_Module_prelude_formatter(v_a_281_, v_a_282_, v_a_283_, v_a_284_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
return v_res_286_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7(){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_294_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_295_ = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
v___x_296_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___closed__0));
v___x_297_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_formatter___boxed), 5, 0);
v___x_298_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_294_, v___x_295_, v___x_296_, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_299_;
v_res_299_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7();
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7___boxed(lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_formatter__7();
return v_res_301_;
}
}
lean_object* l_Lean_Parser_Module_public_formatter(lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = ((lean_object*)(l_Lean_Parser_Module_public_formatter___closed__0));
v___x_320_ = ((lean_object*)(l_Lean_Parser_Module_public_formatter___closed__2));
v___x_321_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_319_, v___x_320_, v_a_314_, v_a_315_, v_a_316_, v_a_317_);
return v___x_321_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_public_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_314_ = stack[0].m_obj;
lean_object* v_a_315_ = stack[1].m_obj;
lean_object* v_a_316_ = stack[2].m_obj;
lean_object* v_a_317_ = stack[3].m_obj;
lean_object* v_res_322_;
v_res_322_ = l_Lean_Parser_Module_public_formatter(v_a_314_, v_a_315_, v_a_316_, v_a_317_);
stack->m_obj
 = v_res_322_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_formatter___boxed(lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Parser_Module_public_formatter(v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
return v_res_328_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11(){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_336_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_337_ = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
v___x_338_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___closed__0));
v___x_339_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_formatter___boxed), 5, 0);
v___x_340_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_336_, v___x_337_, v___x_338_, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_341_;
v_res_341_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11();
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11___boxed(lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_formatter__11();
return v_res_343_;
}
}
lean_object* l_Lean_Parser_Module_meta_formatter(lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = ((lean_object*)(l_Lean_Parser_Module_meta_formatter___closed__0));
v___x_362_ = ((lean_object*)(l_Lean_Parser_Module_meta_formatter___closed__2));
v___x_363_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_361_, v___x_362_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
return v___x_363_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_meta_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_356_ = stack[0].m_obj;
lean_object* v_a_357_ = stack[1].m_obj;
lean_object* v_a_358_ = stack[2].m_obj;
lean_object* v_a_359_ = stack[3].m_obj;
lean_object* v_res_364_;
v_res_364_ = l_Lean_Parser_Module_meta_formatter(v_a_356_, v_a_357_, v_a_358_, v_a_359_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_formatter___boxed(lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Parser_Module_meta_formatter(v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
return v_res_370_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15(){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_378_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_379_ = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
v___x_380_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___closed__0));
v___x_381_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_formatter___boxed), 5, 0);
v___x_382_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_378_, v___x_379_, v___x_380_, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_383_;
v_res_383_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15();
stack->m_obj
 = v_res_383_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15___boxed(lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_formatter__15();
return v_res_385_;
}
}
lean_object* l_Lean_Parser_Module_all_formatter(lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = ((lean_object*)(l_Lean_Parser_Module_all_formatter___closed__0));
v___x_404_ = ((lean_object*)(l_Lean_Parser_Module_all_formatter___closed__2));
v___x_405_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_403_, v___x_404_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
return v___x_405_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_all_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_398_ = stack[0].m_obj;
lean_object* v_a_399_ = stack[1].m_obj;
lean_object* v_a_400_ = stack[2].m_obj;
lean_object* v_a_401_ = stack[3].m_obj;
lean_object* v_res_406_;
v_res_406_ = l_Lean_Parser_Module_all_formatter(v_a_398_, v_a_399_, v_a_400_, v_a_401_);
stack->m_obj
 = v_res_406_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_formatter___boxed(lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Parser_Module_all_formatter(v_a_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
return v_res_412_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19(){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_421_ = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
v___x_422_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___closed__0));
v___x_423_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_formatter___boxed), 5, 0);
v___x_424_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_420_, v___x_421_, v___x_422_, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_425_;
v_res_425_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19();
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19___boxed(lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_formatter__19();
return v_res_427_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__1(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_formatter___boxed), 5, 0);
v___x_436_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__2(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_formatter___boxed), 5, 0);
v___x_438_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__4(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = ((lean_object*)(l_Lean_Parser_Module_import_formatter___closed__3));
v___x_442_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__2, &l_Lean_Parser_Module_import_formatter___closed__2_once, _init_l_Lean_Parser_Module_import_formatter___closed__2);
v___x_443_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_443_, 0, v___x_442_);
lean_closure_set(v___x_443_, 1, v___x_441_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__5(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__4, &l_Lean_Parser_Module_import_formatter___closed__4_once, _init_l_Lean_Parser_Module_import_formatter___closed__4);
v___x_445_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__1, &l_Lean_Parser_Module_import_formatter___closed__1_once, _init_l_Lean_Parser_Module_import_formatter___closed__1);
v___x_446_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_446_, 0, v___x_445_);
lean_closure_set(v___x_446_, 1, v___x_444_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__6(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__5, &l_Lean_Parser_Module_import_formatter___closed__5_once, _init_l_Lean_Parser_Module_import_formatter___closed__5);
v___x_448_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__7(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_formatter___boxed), 5, 0);
v___x_450_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__9(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = ((lean_object*)(l_Lean_Parser_Module_import_formatter___closed__8));
v___x_453_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__7, &l_Lean_Parser_Module_import_formatter___closed__7_once, _init_l_Lean_Parser_Module_import_formatter___closed__7);
v___x_454_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_454_, 0, v___x_453_);
lean_closure_set(v___x_454_, 1, v___x_452_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__10(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__9, &l_Lean_Parser_Module_import_formatter___closed__9_once, _init_l_Lean_Parser_Module_import_formatter___closed__9);
v___x_456_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__6, &l_Lean_Parser_Module_import_formatter___closed__6_once, _init_l_Lean_Parser_Module_import_formatter___closed__6);
v___x_457_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_457_, 0, v___x_456_);
lean_closure_set(v___x_457_, 1, v___x_455_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_formatter___closed__11(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_458_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__10, &l_Lean_Parser_Module_import_formatter___closed__10_once, _init_l_Lean_Parser_Module_import_formatter___closed__10);
v___x_459_ = lean_unsigned_to_nat(1024u);
v___x_460_ = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
v___x_461_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_461_, 0, v___x_460_);
lean_closure_set(v___x_461_, 1, v___x_459_);
lean_closure_set(v___x_461_, 2, v___x_458_);
return v___x_461_;
}
}
lean_object* l_Lean_Parser_Module_import_formatter(lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = ((lean_object*)(l_Lean_Parser_Module_import_formatter___closed__0));
v___x_468_ = lean_obj_once(&l_Lean_Parser_Module_import_formatter___closed__11, &l_Lean_Parser_Module_import_formatter___closed__11_once, _init_l_Lean_Parser_Module_import_formatter___closed__11);
v___x_469_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_467_, v___x_468_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
return v___x_469_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_import_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_462_ = stack[0].m_obj;
lean_object* v_a_463_ = stack[1].m_obj;
lean_object* v_a_464_ = stack[2].m_obj;
lean_object* v_a_465_ = stack[3].m_obj;
lean_object* v_res_470_;
v_res_470_ = l_Lean_Parser_Module_import_formatter(v_a_462_, v_a_463_, v_a_464_, v_a_465_);
stack->m_obj
 = v_res_470_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_formatter___boxed(lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Parser_Module_import_formatter(v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
return v_res_476_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23(){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_484_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_485_ = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
v___x_486_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___closed__0));
v___x_487_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_formatter___boxed), 5, 0);
v___x_488_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_484_, v___x_485_, v___x_486_, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_489_;
v_res_489_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23();
stack->m_obj
 = v_res_489_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23___boxed(lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_formatter__23();
return v_res_491_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__1(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
lean_inc_ref(v___x_499_);
v___x_500_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_500_, 0, v___x_499_);
lean_closure_set(v___x_500_, 1, v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__2(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__1, &l_Lean_Parser_Module_header_formatter___closed__1_once, _init_l_Lean_Parser_Module_header_formatter___closed__1);
v___x_502_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_formatter___boxed), 5, 0);
v___x_503_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_503_, 0, v___x_502_);
lean_closure_set(v___x_503_, 1, v___x_501_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__3(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__2, &l_Lean_Parser_Module_header_formatter___closed__2_once, _init_l_Lean_Parser_Module_header_formatter___closed__2);
v___x_505_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__4(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
v___x_507_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_formatter___boxed), 5, 0);
v___x_508_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_508_, 0, v___x_507_);
lean_closure_set(v___x_508_, 1, v___x_506_);
return v___x_508_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__5(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__4, &l_Lean_Parser_Module_header_formatter___closed__4_once, _init_l_Lean_Parser_Module_header_formatter___closed__4);
v___x_510_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__6(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
v___x_512_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_formatter___boxed), 5, 0);
v___x_513_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_513_, 0, v___x_512_);
lean_closure_set(v___x_513_, 1, v___x_511_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__7(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__6, &l_Lean_Parser_Module_header_formatter___closed__6_once, _init_l_Lean_Parser_Module_header_formatter___closed__6);
v___x_515_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__8(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
v___x_517_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__7, &l_Lean_Parser_Module_header_formatter___closed__7_once, _init_l_Lean_Parser_Module_header_formatter___closed__7);
v___x_518_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_518_, 0, v___x_517_);
lean_closure_set(v___x_518_, 1, v___x_516_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__9(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__8, &l_Lean_Parser_Module_header_formatter___closed__8_once, _init_l_Lean_Parser_Module_header_formatter___closed__8);
v___x_520_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__5, &l_Lean_Parser_Module_header_formatter___closed__5_once, _init_l_Lean_Parser_Module_header_formatter___closed__5);
v___x_521_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_521_, 0, v___x_520_);
lean_closure_set(v___x_521_, 1, v___x_519_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__10(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__9, &l_Lean_Parser_Module_header_formatter___closed__9_once, _init_l_Lean_Parser_Module_header_formatter___closed__9);
v___x_523_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__3, &l_Lean_Parser_Module_header_formatter___closed__3_once, _init_l_Lean_Parser_Module_header_formatter___closed__3);
v___x_524_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_524_, 0, v___x_523_);
lean_closure_set(v___x_524_, 1, v___x_522_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_formatter___closed__11(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_525_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__10, &l_Lean_Parser_Module_header_formatter___closed__10_once, _init_l_Lean_Parser_Module_header_formatter___closed__10);
v___x_526_ = lean_unsigned_to_nat(1024u);
v___x_527_ = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
v___x_528_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_528_, 0, v___x_527_);
lean_closure_set(v___x_528_, 1, v___x_526_);
lean_closure_set(v___x_528_, 2, v___x_525_);
return v___x_528_;
}
}
lean_object* l_Lean_Parser_Module_header_formatter(lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = ((lean_object*)(l_Lean_Parser_Module_header_formatter___closed__0));
v___x_535_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__11, &l_Lean_Parser_Module_header_formatter___closed__11_once, _init_l_Lean_Parser_Module_header_formatter___closed__11);
v___x_536_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_534_, v___x_535_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
return v___x_536_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_header_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_529_ = stack[0].m_obj;
lean_object* v_a_530_ = stack[1].m_obj;
lean_object* v_a_531_ = stack[2].m_obj;
lean_object* v_a_532_ = stack[3].m_obj;
lean_object* v_res_537_;
v_res_537_ = l_Lean_Parser_Module_header_formatter(v_a_529_, v_a_530_, v_a_531_, v_a_532_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_formatter___boxed(lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Parser_Module_header_formatter(v_a_538_, v_a_539_, v_a_540_, v_a_541_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
return v_res_543_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27(){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_551_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_552_ = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
v___x_553_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___closed__0));
v___x_554_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_formatter___boxed), 5, 0);
v___x_555_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_551_, v___x_552_, v___x_553_, v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_556_;
v_res_556_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27();
stack->m_obj
 = v_res_556_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27___boxed(lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_formatter__27();
return v_res_558_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__3(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_obj_once(&l_Lean_Parser_Module_header_formatter___closed__1, &l_Lean_Parser_Module_header_formatter___closed__1_once, _init_l_Lean_Parser_Module_header_formatter___closed__1);
v___x_574_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__2));
v___x_575_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_575_, 0, v___x_574_);
lean_closure_set(v___x_575_, 1, v___x_573_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__4(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_obj_once(&l_Lean_Parser_Module_module_formatter___closed__3, &l_Lean_Parser_Module_module_formatter___closed__3_once, _init_l_Lean_Parser_Module_module_formatter___closed__3);
v___x_577_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__5(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_obj_once(&l_Lean_Parser_Module_module_formatter___closed__4, &l_Lean_Parser_Module_module_formatter___closed__4_once, _init_l_Lean_Parser_Module_module_formatter___closed__4);
v___x_579_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_formatter___boxed), 5, 0);
v___x_580_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_580_, 0, v___x_579_);
lean_closure_set(v___x_580_, 1, v___x_578_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_formatter___closed__6(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = lean_obj_once(&l_Lean_Parser_Module_module_formatter___closed__5, &l_Lean_Parser_Module_module_formatter___closed__5_once, _init_l_Lean_Parser_Module_module_formatter___closed__5);
v___x_582_ = lean_unsigned_to_nat(1024u);
v___x_583_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_584_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_584_, 0, v___x_583_);
lean_closure_set(v___x_584_, 1, v___x_582_);
lean_closure_set(v___x_584_, 2, v___x_581_);
return v___x_584_;
}
}
lean_object* l_Lean_Parser_Module_module_formatter(lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__1));
v___x_591_ = lean_obj_once(&l_Lean_Parser_Module_module_formatter___closed__6, &l_Lean_Parser_Module_module_formatter___closed__6_once, _init_l_Lean_Parser_Module_module_formatter___closed__6);
v___x_592_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_590_, v___x_591_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
return v___x_592_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_module_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_585_ = stack[0].m_obj;
lean_object* v_a_586_ = stack[1].m_obj;
lean_object* v_a_587_ = stack[2].m_obj;
lean_object* v_a_588_ = stack[3].m_obj;
lean_object* v_res_593_;
v_res_593_ = l_Lean_Parser_Module_module_formatter(v_a_585_, v_a_586_, v_a_587_, v_a_588_);
stack->m_obj
 = v_res_593_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_formatter___boxed(lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Parser_Module_module_formatter(v_a_594_, v_a_595_, v_a_596_, v_a_597_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
return v_res_599_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31(){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_607_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_608_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_609_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___closed__0));
v___x_610_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_formatter___boxed), 5, 0);
v___x_611_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_607_, v___x_608_, v___x_609_, v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_612_;
v_res_612_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31();
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31___boxed(lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_formatter__31();
return v_res_614_;
}
}
lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer(lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__0));
v___x_634_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk_parenthesizer___closed__2));
v___x_635_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_633_, v___x_634_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
return v___x_635_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_moduleTk_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_628_ = stack[0].m_obj;
lean_object* v_a_629_ = stack[1].m_obj;
lean_object* v_a_630_ = stack[2].m_obj;
lean_object* v_a_631_ = stack[3].m_obj;
lean_object* v_res_636_;
v_res_636_ = l_Lean_Parser_Module_moduleTk_parenthesizer(v_a_628_, v_a_629_, v_a_630_, v_a_631_);
stack->m_obj
 = v_res_636_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer___boxed(lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Parser_Module_moduleTk_parenthesizer(v_a_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
return v_res_642_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35(){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_651_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_652_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__4));
v___x_653_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___closed__1));
v___x_654_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_parenthesizer___boxed), 5, 0);
v___x_655_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_651_, v___x_652_, v___x_653_, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_656_;
v_res_656_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35();
stack->m_obj
 = v_res_656_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35___boxed(lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__35();
return v_res_658_;
}
}
lean_object* l_Lean_Parser_Module_prelude_parenthesizer(lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = ((lean_object*)(l_Lean_Parser_Module_prelude_parenthesizer___closed__0));
v___x_678_ = ((lean_object*)(l_Lean_Parser_Module_prelude_parenthesizer___closed__2));
v___x_679_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_677_, v___x_678_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
return v___x_679_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_prelude_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_672_ = stack[0].m_obj;
lean_object* v_a_673_ = stack[1].m_obj;
lean_object* v_a_674_ = stack[2].m_obj;
lean_object* v_a_675_ = stack[3].m_obj;
lean_object* v_res_680_;
v_res_680_ = l_Lean_Parser_Module_prelude_parenthesizer(v_a_672_, v_a_673_, v_a_674_, v_a_675_);
stack->m_obj
 = v_res_680_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_parenthesizer___boxed(lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Parser_Module_prelude_parenthesizer(v_a_681_, v_a_682_, v_a_683_, v_a_684_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
return v_res_686_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39(){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_694_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_695_ = ((lean_object*)(l_Lean_Parser_Module_prelude___closed__1));
v___x_696_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___closed__0));
v___x_697_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_parenthesizer___boxed), 5, 0);
v___x_698_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_694_, v___x_695_, v___x_696_, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_699_;
v_res_699_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39();
stack->m_obj
 = v_res_699_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39___boxed(lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__39();
return v_res_701_;
}
}
lean_object* l_Lean_Parser_Module_public_parenthesizer(lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = ((lean_object*)(l_Lean_Parser_Module_public_parenthesizer___closed__0));
v___x_720_ = ((lean_object*)(l_Lean_Parser_Module_public_parenthesizer___closed__2));
v___x_721_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_719_, v___x_720_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_721_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_public_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_714_ = stack[0].m_obj;
lean_object* v_a_715_ = stack[1].m_obj;
lean_object* v_a_716_ = stack[2].m_obj;
lean_object* v_a_717_ = stack[3].m_obj;
lean_object* v_res_722_;
v_res_722_ = l_Lean_Parser_Module_public_parenthesizer(v_a_714_, v_a_715_, v_a_716_, v_a_717_);
stack->m_obj
 = v_res_722_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_public_parenthesizer___boxed(lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Parser_Module_public_parenthesizer(v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
return v_res_728_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43(){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_736_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_737_ = ((lean_object*)(l_Lean_Parser_Module_public___closed__1));
v___x_738_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___closed__0));
v___x_739_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_parenthesizer___boxed), 5, 0);
v___x_740_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_736_, v___x_737_, v___x_738_, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_741_;
v_res_741_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43();
stack->m_obj
 = v_res_741_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43___boxed(lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_public_parenthesizer__43();
return v_res_743_;
}
}
lean_object* l_Lean_Parser_Module_meta_parenthesizer(lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = ((lean_object*)(l_Lean_Parser_Module_meta_parenthesizer___closed__0));
v___x_762_ = ((lean_object*)(l_Lean_Parser_Module_meta_parenthesizer___closed__2));
v___x_763_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_761_, v___x_762_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
return v___x_763_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_meta_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_756_ = stack[0].m_obj;
lean_object* v_a_757_ = stack[1].m_obj;
lean_object* v_a_758_ = stack[2].m_obj;
lean_object* v_a_759_ = stack[3].m_obj;
lean_object* v_res_764_;
v_res_764_ = l_Lean_Parser_Module_meta_parenthesizer(v_a_756_, v_a_757_, v_a_758_, v_a_759_);
stack->m_obj
 = v_res_764_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_meta_parenthesizer___boxed(lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Parser_Module_meta_parenthesizer(v_a_765_, v_a_766_, v_a_767_, v_a_768_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
return v_res_770_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47(){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_778_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_779_ = ((lean_object*)(l_Lean_Parser_Module_meta___closed__1));
v___x_780_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___closed__0));
v___x_781_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_parenthesizer___boxed), 5, 0);
v___x_782_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_778_, v___x_779_, v___x_780_, v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_783_;
v_res_783_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47();
stack->m_obj
 = v_res_783_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47___boxed(lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_meta_parenthesizer__47();
return v_res_785_;
}
}
lean_object* l_Lean_Parser_Module_all_parenthesizer(lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = ((lean_object*)(l_Lean_Parser_Module_all_parenthesizer___closed__0));
v___x_804_ = ((lean_object*)(l_Lean_Parser_Module_all_parenthesizer___closed__2));
v___x_805_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_803_, v___x_804_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
return v___x_805_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_all_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_798_ = stack[0].m_obj;
lean_object* v_a_799_ = stack[1].m_obj;
lean_object* v_a_800_ = stack[2].m_obj;
lean_object* v_a_801_ = stack[3].m_obj;
lean_object* v_res_806_;
v_res_806_ = l_Lean_Parser_Module_all_parenthesizer(v_a_798_, v_a_799_, v_a_800_, v_a_801_);
stack->m_obj
 = v_res_806_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_parenthesizer___boxed(lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Parser_Module_all_parenthesizer(v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
return v_res_812_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51(){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_820_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_821_ = ((lean_object*)(l_Lean_Parser_Module_all___closed__1));
v___x_822_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___closed__0));
v___x_823_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_parenthesizer___boxed), 5, 0);
v___x_824_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_820_, v___x_821_, v___x_822_, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_825_;
v_res_825_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51();
stack->m_obj
 = v_res_825_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51___boxed(lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_all_parenthesizer__51();
return v_res_827_;
}
}
lean_object* l_Lean_Parser_Module_import_parenthesizer___lam__0(lean_object* v___x_828_, lean_object* v___x_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_828_, v___x_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
return v___x_835_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_import_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_828_ = stack[0].m_obj;
lean_object* v___x_829_ = stack[1].m_obj;
lean_object* v___y_830_ = stack[2].m_obj;
lean_object* v___y_831_ = stack[3].m_obj;
lean_object* v___y_832_ = stack[4].m_obj;
lean_object* v___y_833_ = stack[5].m_obj;
lean_object* v_res_836_;
v_res_836_ = l_Lean_Parser_Module_import_parenthesizer___lam__0(v___x_828_, v___x_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
stack->m_obj
 = v_res_836_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___lam__0___boxed(lean_object* v___x_837_, lean_object* v___x_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Parser_Module_import_parenthesizer___lam__0(v___x_837_, v___x_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
return v_res_844_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_public_parenthesizer___boxed), 5, 0);
v___x_853_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_meta_parenthesizer___boxed), 5, 0);
v___x_855_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = ((lean_object*)(l_Lean_Parser_Module_import_parenthesizer___closed__3));
v___x_859_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__2, &l_Lean_Parser_Module_import_parenthesizer___closed__2_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__2);
v___x_860_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_860_, 0, v___x_859_);
lean_closure_set(v___x_860_, 1, v___x_858_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___f_863_; 
v___x_861_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__4, &l_Lean_Parser_Module_import_parenthesizer___closed__4_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__4);
v___x_862_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__1, &l_Lean_Parser_Module_import_parenthesizer___closed__1_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__1);
v___f_863_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_863_, 0, v___x_862_);
lean_closure_set(v___f_863_, 1, v___x_861_);
return v___f_863_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_parenthesizer___boxed), 5, 0);
v___x_865_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = ((lean_object*)(l_Lean_Parser_Module_import_parenthesizer___closed__7));
v___x_868_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__6, &l_Lean_Parser_Module_import_parenthesizer___closed__6_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__6);
v___x_869_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_869_, 0, v___x_868_);
lean_closure_set(v___x_869_, 1, v___x_867_);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_870_; lean_object* v___f_871_; lean_object* v___x_872_; 
v___x_870_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__8, &l_Lean_Parser_Module_import_parenthesizer___closed__8_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__8);
v___f_871_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__5, &l_Lean_Parser_Module_import_parenthesizer___closed__5_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__5);
v___x_872_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_872_, 0, v___f_871_);
lean_closure_set(v___x_872_, 1, v___x_870_);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_Parser_Module_import_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_873_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__9, &l_Lean_Parser_Module_import_parenthesizer___closed__9_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__9);
v___x_874_ = lean_unsigned_to_nat(1024u);
v___x_875_ = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
v___x_876_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_876_, 0, v___x_875_);
lean_closure_set(v___x_876_, 1, v___x_874_);
lean_closure_set(v___x_876_, 2, v___x_873_);
return v___x_876_;
}
}
lean_object* l_Lean_Parser_Module_import_parenthesizer(lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = ((lean_object*)(l_Lean_Parser_Module_import_parenthesizer___closed__0));
v___x_883_ = lean_obj_once(&l_Lean_Parser_Module_import_parenthesizer___closed__10, &l_Lean_Parser_Module_import_parenthesizer___closed__10_once, _init_l_Lean_Parser_Module_import_parenthesizer___closed__10);
v___x_884_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_882_, v___x_883_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
return v___x_884_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_import_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_877_ = stack[0].m_obj;
lean_object* v_a_878_ = stack[1].m_obj;
lean_object* v_a_879_ = stack[2].m_obj;
lean_object* v_a_880_ = stack[3].m_obj;
lean_object* v_res_885_;
v_res_885_ = l_Lean_Parser_Module_import_parenthesizer(v_a_877_, v_a_878_, v_a_879_, v_a_880_);
stack->m_obj
 = v_res_885_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___boxed(lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Parser_Module_import_parenthesizer(v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
return v_res_891_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55(){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_899_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_900_ = ((lean_object*)(l_Lean_Parser_Module_import___closed__1));
v___x_901_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___closed__0));
v___x_902_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer___boxed), 5, 0);
v___x_903_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_899_, v___x_900_, v___x_901_, v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_904_;
v_res_904_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55();
stack->m_obj
 = v_res_904_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55___boxed(lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_import_parenthesizer__55();
return v_res_906_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__2));
v___x_918_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_parenthesizer___boxed), 5, 0);
v___x_919_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_919_, 0, v___x_918_);
lean_closure_set(v___x_919_, 1, v___x_917_);
return v___x_919_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__3, &l_Lean_Parser_Module_header_parenthesizer___closed__3_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__3);
v___x_921_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__1));
v___x_923_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_parenthesizer___boxed), 5, 0);
v___x_924_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_924_, 0, v___x_923_);
lean_closure_set(v___x_924_, 1, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__5, &l_Lean_Parser_Module_header_parenthesizer___closed__5_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__5);
v___x_926_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__1));
v___x_928_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer___boxed), 5, 0);
v___x_929_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_929_, 0, v___x_928_);
lean_closure_set(v___x_929_, 1, v___x_927_);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__7, &l_Lean_Parser_Module_header_parenthesizer___closed__7_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__7);
v___x_931_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__1));
v___x_933_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__8, &l_Lean_Parser_Module_header_parenthesizer___closed__8_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__8);
v___x_934_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_934_, 0, v___x_933_);
lean_closure_set(v___x_934_, 1, v___x_932_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__9, &l_Lean_Parser_Module_header_parenthesizer___closed__9_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__9);
v___x_936_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__6, &l_Lean_Parser_Module_header_parenthesizer___closed__6_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__6);
v___x_937_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_937_, 0, v___x_936_);
lean_closure_set(v___x_937_, 1, v___x_935_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__10, &l_Lean_Parser_Module_header_parenthesizer___closed__10_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__10);
v___x_939_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__4, &l_Lean_Parser_Module_header_parenthesizer___closed__4_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__4);
v___x_940_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_940_, 0, v___x_939_);
lean_closure_set(v___x_940_, 1, v___x_938_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_Parser_Module_header_parenthesizer___closed__12(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_941_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__11, &l_Lean_Parser_Module_header_parenthesizer___closed__11_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__11);
v___x_942_ = lean_unsigned_to_nat(1024u);
v___x_943_ = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
v___x_944_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_944_, 0, v___x_943_);
lean_closure_set(v___x_944_, 1, v___x_942_);
lean_closure_set(v___x_944_, 2, v___x_941_);
return v___x_944_;
}
}
lean_object* l_Lean_Parser_Module_header_parenthesizer(lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = ((lean_object*)(l_Lean_Parser_Module_header_parenthesizer___closed__0));
v___x_951_ = lean_obj_once(&l_Lean_Parser_Module_header_parenthesizer___closed__12, &l_Lean_Parser_Module_header_parenthesizer___closed__12_once, _init_l_Lean_Parser_Module_header_parenthesizer___closed__12);
v___x_952_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_950_, v___x_951_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
return v___x_952_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_header_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_945_ = stack[0].m_obj;
lean_object* v_a_946_ = stack[1].m_obj;
lean_object* v_a_947_ = stack[2].m_obj;
lean_object* v_a_948_ = stack[3].m_obj;
lean_object* v_res_953_;
v_res_953_ = l_Lean_Parser_Module_header_parenthesizer(v_a_945_, v_a_946_, v_a_947_, v_a_948_);
stack->m_obj
 = v_res_953_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer___boxed(lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Parser_Module_header_parenthesizer(v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
return v_res_959_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59(){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_967_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_968_ = ((lean_object*)(l_Lean_Parser_Module_header___closed__1));
v___x_969_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___closed__0));
v___x_970_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_parenthesizer___boxed), 5, 0);
v___x_971_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_967_, v___x_968_, v___x_969_, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_972_;
v_res_972_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59();
stack->m_obj
 = v_res_972_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59___boxed(lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_header_parenthesizer__59();
return v_res_974_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = ((lean_object*)(l_Lean_Parser_Module_module_parenthesizer___closed__3));
v___x_990_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_parenthesizer___boxed), 5, 0);
v___x_991_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_991_, 0, v___x_990_);
lean_closure_set(v___x_991_, 1, v___x_989_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_992_ = lean_obj_once(&l_Lean_Parser_Module_module_parenthesizer___closed__4, &l_Lean_Parser_Module_module_parenthesizer___closed__4_once, _init_l_Lean_Parser_Module_module_parenthesizer___closed__4);
v___x_993_ = lean_unsigned_to_nat(1024u);
v___x_994_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_995_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_995_, 0, v___x_994_);
lean_closure_set(v___x_995_, 1, v___x_993_);
lean_closure_set(v___x_995_, 2, v___x_992_);
return v___x_995_;
}
}
lean_object* l_Lean_Parser_Module_module_parenthesizer(lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = ((lean_object*)(l_Lean_Parser_Module_module_parenthesizer___closed__0));
v___x_1002_ = lean_obj_once(&l_Lean_Parser_Module_module_parenthesizer___closed__5, &l_Lean_Parser_Module_module_parenthesizer___closed__5_once, _init_l_Lean_Parser_Module_module_parenthesizer___closed__5);
v___x_1003_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1001_, v___x_1002_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
return v___x_1003_;
}
}
LEAN_EXPORT void l_Lean_Parser_Module_module_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_996_ = stack[0].m_obj;
lean_object* v_a_997_ = stack[1].m_obj;
lean_object* v_a_998_ = stack[2].m_obj;
lean_object* v_a_999_ = stack[3].m_obj;
lean_object* v_res_1004_;
v_res_1004_ = l_Lean_Parser_Module_module_parenthesizer(v_a_996_, v_a_997_, v_a_998_, v_a_999_);
stack->m_obj
 = v_res_1004_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_parenthesizer___boxed(lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Parser_Module_module_parenthesizer(v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
return v_res_1010_;
}
}
lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63(){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1018_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1019_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_1020_ = ((lean_object*)(l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___closed__0));
v___x_1021_ = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_parenthesizer___boxed), 5, 0);
v___x_1022_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1018_, v___x_1019_, v___x_1020_, v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1023_;
v_res_1023_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63();
stack->m_obj
 = v_res_1023_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63___boxed(lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l___private_Lean_Parser_Module_Syntax_0__Lean_Parser_Module_module___regBuiltin_Lean_Parser_Module_module_parenthesizer__63();
return v_res_1025_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__0(void){
_start:
{
uint8_t v___x_1026_; uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1026_ = 0;
v___x_1027_ = 1;
v___x_1028_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_1029_ = ((lean_object*)(l_Lean_Parser_Module_moduleTk___closed__6));
v___x_1030_ = l_Lean_Parser_mkAntiquot(v___x_1029_, v___x_1028_, v___x_1027_, v___x_1026_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__3(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_unsigned_to_nat(0u);
v___x_1035_ = ((lean_object*)(l_Lean_Parser_Module_module___closed__2));
v___x_1036_ = l_Lean_Parser_categoryParser(v___x_1035_, v___x_1034_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__4(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = lean_obj_once(&l_Lean_Parser_Module_header___closed__3, &l_Lean_Parser_Module_header___closed__3_once, _init_l_Lean_Parser_Module_header___closed__3);
v___x_1038_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__3, &l_Lean_Parser_Module_module___closed__3_once, _init_l_Lean_Parser_Module_module___closed__3);
v___x_1039_ = l_Lean_Parser_andthen(v___x_1038_, v___x_1037_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__5(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__4, &l_Lean_Parser_Module_module___closed__4_once, _init_l_Lean_Parser_Module_module___closed__4);
v___x_1041_ = l_Lean_Parser_many(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__6(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__5, &l_Lean_Parser_Module_module___closed__5_once, _init_l_Lean_Parser_Module_module___closed__5);
v___x_1043_ = l_Lean_Parser_Module_header;
v___x_1044_ = l_Lean_Parser_andthen(v___x_1043_, v___x_1042_);
return v___x_1044_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__7(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1045_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__6, &l_Lean_Parser_Module_module___closed__6_once, _init_l_Lean_Parser_Module_module___closed__6);
v___x_1046_ = lean_unsigned_to_nat(1024u);
v___x_1047_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_1048_ = l_Lean_Parser_leadingNode(v___x_1047_, v___x_1046_, v___x_1045_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__8(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__7, &l_Lean_Parser_Module_module___closed__7_once, _init_l_Lean_Parser_Module_module___closed__7);
v___x_1050_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__0, &l_Lean_Parser_Module_module___closed__0_once, _init_l_Lean_Parser_Module_module___closed__0);
v___x_1051_ = l_Lean_Parser_withAntiquot(v___x_1050_, v___x_1049_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module___closed__9(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__8, &l_Lean_Parser_Module_module___closed__8_once, _init_l_Lean_Parser_Module_module___closed__8);
v___x_1053_ = ((lean_object*)(l_Lean_Parser_Module_module_formatter___closed__0));
v___x_1054_ = l_Lean_Parser_withCache(v___x_1053_, v___x_1052_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_Parser_Module_module(void){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_obj_once(&l_Lean_Parser_Module_module___closed__9, &l_Lean_Parser_Module_module___closed__9_once, _init_l_Lean_Parser_Module_module___closed__9);
return v___x_1055_;
}
}
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Module_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
