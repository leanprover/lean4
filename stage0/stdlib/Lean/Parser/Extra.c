// Lean compiler output
// Module: Lean.Parser.Extra
// Imports: public import Lean.PrettyPrinter.Formatter public import Lean.PrettyPrinter.Parenthesizer import all Lean.Parser.Types import all Lean.Parser.Basic import all Lean.Parser.Extension public meta import Lean.Hygiene
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
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_termParser_formatter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Parser_termParser_formatter___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_termParser_formatter___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Parser_termParser_formatter___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_termParser_formatter___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Parser_termParser_formatter___redArg___closed__1 = (const lean_object*)&l_Lean_Parser_termParser_formatter___redArg___closed__1_value;
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_commandParser_formatter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Parser_commandParser_formatter___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_commandParser_formatter___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Parser_commandParser_formatter___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_commandParser_formatter___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_Parser_commandParser_formatter___redArg___closed__1 = (const lean_object*)&l_Lean_Parser_commandParser_formatter___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_atomic_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_atomic_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_termParser_formatter___redArg___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__0_value;
static const lean_string_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "antiquotNestedExpr"};
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value;
static const lean_ctor_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(4, 217, 111, 200, 191, 162, 168, 125)}};
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__2_value;
static const lean_string_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__4_value;
static const lean_string_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__7_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__4_value),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__7_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__8_value;
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value;
static const lean_string_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value;
static const lean_string_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2 = (const lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 184, 198, 144, 189, 249, 117, 153)}};
static const lean_ctor_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_2),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2_value),LEAN_SCALAR_PTR_LITERAL(153, 167, 177, 159, 214, 65, 137, 70)}};
static const lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3 = (const lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value;
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15();
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_antiquotExpr_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Parser_antiquotExpr_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_antiquotExpr_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_antiquotExpr_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotExpr_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_antiquotExpr_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_antiquotExpr_formatter___closed__1_value;
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotExpr_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "antiquotName"};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 48, 35, 197, 163, 216, 250, 79)}};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1_value;
static const lean_string_object l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3_value;
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__0_value;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__1_value;
static const lean_string_object l_Lean_Parser_mkAntiquot_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "antiquot"};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__2_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquot_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 141, 12, 45, 178, 67, 53, 106)}};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__3_value;
static const lean_string_object l_Lean_Parser_mkAntiquot_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___lam__2___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__7_value;
lean_object* l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__7_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__8_value;
static const lean_string_object l_Lean_Parser_mkAntiquot_formatter___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "pseudo"};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__9 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__9_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquot_formatter___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__9_value),LEAN_SCALAR_PTR_LITERAL(246, 255, 48, 87, 29, 98, 48, 237)}};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__10 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__10_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2_value;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__0_value),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4_value;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parenthesizer"};
static const lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 184, 198, 144, 189, 249, 117, 153)}};
static const lean_ctor_object l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 86, 214, 3, 200, 227, 238, 166)}};
static const lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value;
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35();
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_antiquotExpr_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotExpr_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_antiquotExpr_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_antiquotExpr_parenthesizer___closed__0_value;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotExpr_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0_value;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_mkAntiquot_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquot_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquot_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_mkAntiquot_parenthesizer___closed__2_value;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "antiquot_scope"};
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 75, 125, 66, 98, 92, 21, 108)}};
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__1_value;
static const lean_string_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__3_value;
static const lean_string_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__4_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__5_value;
static const lean_string_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_sepByElemParser_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sepBy"};
static const lean_object* l_Lean_Parser_sepByElemParser_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_sepByElemParser_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_sepByElemParser_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_sepByElemParser_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 56, 254, 223, 11, 70, 55, 147)}};
static const lean_object* l_Lean_Parser_sepByElemParser_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_sepByElemParser_formatter___closed__1_value;
static const lean_string_object l_Lean_Parser_sepByElemParser_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lean_Parser_sepByElemParser_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_sepByElemParser_formatter___closed__2_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_formatter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_optional_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_optional_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_optional_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_optional_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_optional_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_optional_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_optional_formatter___closed__1_value;
static const lean_string_object l_Lean_Parser_optional_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Parser_optional_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_optional_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_optional_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_optional_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_optional_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_optional_formatter___closed__3_value;
lean_object* l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_optional_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_optional_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_optional_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_optional_parenthesizer___closed__0_value;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
static lean_object* l_Lean_Parser_optional___closed__0;
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_optional_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 167, 191, 130, 216, 220, 182, 40)}};
static const lean_object* l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value;
static const lean_string_object l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 507, .m_capacity = 507, .m_length = 506, .m_data = "The parser `optional(p)`, or `(p)\?`, parses `p` if it succeeds,\notherwise it succeeds with no value.\n\nNote that because `\?` is a legal identifier character, one must write `(p)\?` or `p \?` for\nit to parse correctly. `ident\?` will not work; one must write `(ident)\?` instead.\n\nThis parser has arity 1: it produces a `nullKind` node containing either zero arguments\n(for the `none` case) or the list of arguments produced by `p`.\n(In particular, if `p` has arity 0 then the two cases are not differentiated!) "};
static const lean_object* l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__1_value;
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_many_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Parser_many_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_many_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_many_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_many_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Parser_many_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_many_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_many_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_sepByElemParser_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_many_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_many_formatter___closed__2_value;
lean_object* l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_many_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_sepByElemParser_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_many_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_many_parenthesizer___closed__0_value;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_many___closed__0;
lean_object* l_Lean_Parser_manyNoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many(lean_object*);
static const lean_ctor_object l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_many_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 114, 232, 230, 181, 52, 168, 160)}};
static const lean_object* l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value;
static const lean_string_object l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 390, .m_capacity = 390, .m_length = 389, .m_data = "The parser `many(p)`, or `p*`, repeats `p` until it fails, and returns the list of results.\n\nThe argument `p` is \"auto-grouped\", meaning that if the arity is greater than 1 it will be\nautomatically replaced by `group(p)` to ensure that it produces exactly 1 value.\n\nThis parser has arity 1: it produces a `nullKind` node containing one argument for each\ninvocation of `p` (or `group(p)`). "};
static const lean_object* l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1NoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1(lean_object*);
static const lean_string_object l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 61, 196, 93, 201, 246, 193, 192)}};
static const lean_object* l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 648, .m_capacity = 648, .m_length = 647, .m_data = "The parser `many1(p)`, or `p+`, repeats `p` until it fails, and returns the list of results.\n`p` must succeed at least once, or this parser will fail.\n\nNote that this parser produces the same parse tree as the `many(p)` / `p*` combinator,\nand one matches both `p*` and `p+` using `$[ .. ]*` syntax in a syntax match.\n(There is no `$[ .. ]+` syntax.)\n\nThe argument `p` is \"auto-grouped\", meaning that if the arity is greater than 1 it will be\nautomatically replaced by `group(p)` to ensure that it produces exactly 1 value.\n\nThis parser has arity 1: it produces a `nullKind` node containing one argument for each\ninvocation of `p` (or `group(p)`). "};
static const lean_object* l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_ident_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_ident_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_ident_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ident_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ident_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_ident_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_ident_formatter___closed__1_value;
static lean_object* l_Lean_Parser_ident_formatter___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ident_parenthesizer___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l_Lean_Parser_ident___closed__0;
extern lean_object* l_Lean_Parser_identNoAntiquot;
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_ident___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_ident;
static const lean_ctor_object l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_ident_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 242, 101, 31, 193, 156, 127, 171)}};
static const lean_object* l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value;
static const lean_string_object l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 856, .m_capacity = 856, .m_length = 845, .m_data = "The parser `ident` parses a single identifier, possibly with namespaces, such as `foo` or\n`bar.baz`. The identifier must not be a declared token, so for example it will not match `\"def\"`\nbecause `def` is a keyword token. Tokens are implicitly declared by using them in string literals\nin parser declarations, so `syntax foo := \"bla\"` will make `bla` no longer legal as an identifier.\n\nIdentifiers can contain special characters or keywords if they are escaped using the `«»` characters:\n`«def»` is an identifier named `def`, and `«x»` is treated the same as `x`. This is useful for\nusing disallowed characters in identifiers such as `«foo.bar».baz` or `«hello world»`.\n\nThis parser has arity 1: it produces a `Syntax.ident` node containing the parsed identifier.\nYou can use `TSyntax.getId` to extract the name from the resulting syntax object. "};
static const lean_object* l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__1_value;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__0_value;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_identWithPartialTrailingDot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "no space before"};
static const lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__0 = (const lean_object*)&l_Lean_Parser_identWithPartialTrailingDot___closed__0_value;
lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__1;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__2;
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__3;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__4;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__5;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__6;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot;
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_rawIdent_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_rawIdent_parenthesizer___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_rawIdent_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_rawIdent_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_rawIdentNoAntiquot;
static lean_object* l_Lean_Parser_rawIdent___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent;
static const lean_string_object l_Lean_Parser_hygieneInfo_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Parser_hygieneInfo_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_hygieneInfo_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_hygieneInfo_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_hygieneInfo_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Parser_hygieneInfo_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_hygieneInfo_formatter___closed__1_value;
static lean_object* l_Lean_Parser_hygieneInfo_formatter___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_hygieneInfo_parenthesizer___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_hygieneInfo___closed__0;
extern lean_object* l_Lean_Parser_hygieneInfoNoAntiquot;
static lean_object* l_Lean_Parser_hygieneInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo;
static const lean_ctor_object l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_hygieneInfo_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 96, 174, 177, 221, 86, 223, 51)}};
static const lean_object* l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value;
static const lean_string_object l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1028, .m_capacity = 1028, .m_length = 1026, .m_data = "The parser `hygieneInfo` parses no text, but creates a `hygieneInfoKind` node\ncontaining an anonymous identifier as if it were parsed at the current position.\nThis identifier is modified by syntax quotations to add macro scopes like a regular identifier.\n\nThis is used to implement `have := ...` syntax: the `hygieneInfo` between the `have` and `:=`\ncollects macro scopes, which we can apply to `this` when expanding to `have this := ...`.\nSee [the language reference](lean-manual://section/macro-hygiene) for more information about\nmacro hygiene.\n\nThis is also used to implement cdot functions such as `(1 + ·)`. The opening parenthesis contains\na `hygieneInfo` node as does the cdot, which lets cdot expansion hygienically associate parentheses to cdots.\n\nThis parser has arity 1: it produces a `hygieneInfoKind` node containing an anonymous `Syntax.ident`.\nYou can use `HygieneInfo.mkIdent` to create an `Ident` from the syntax object,\nbut you can also use `TSyntax.getHygieneInfo` to get the raw name from the identifier. "};
static const lean_object* l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_numLit_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Parser_numLit_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_numLit_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_numLit_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_numLit_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Parser_numLit_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_numLit_formatter___closed__1_value;
static lean_object* l_Lean_Parser_numLit_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_numLit_parenthesizer___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_numLit___closed__0;
extern lean_object* l_Lean_Parser_numLitNoAntiquot;
static lean_object* l_Lean_Parser_numLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_numLit;
static const lean_string_object l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "numLit"};
static const lean_object* l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 124, 25, 195, 9, 201, 171, 221)}};
static const lean_object* l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 335, .m_capacity = 335, .m_length = 334, .m_data = "The parser `num` parses a numeric literal in several bases:\n\n* Decimal: `129`\n* Hexadecimal: `0xdeadbeef`\n* Octal: `0o755`\n* Binary: `0b1101`\n\nThis parser has arity 1: it produces a `numLitKind` node containing an atom with the text of the\nliteral.\nYou can use `TSyntax.getNat` to extract the number from the resulting syntax object. "};
static const lean_object* l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_hexnum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l_Lean_Parser_hexnum___closed__0 = (const lean_object*)&l_Lean_Parser_hexnum___closed__0_value;
static const lean_ctor_object l_Lean_Parser_hexnum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_hexnum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l_Lean_Parser_hexnum___closed__1 = (const lean_object*)&l_Lean_Parser_hexnum___closed__1_value;
static lean_object* l_Lean_Parser_hexnum___closed__2;
extern lean_object* l_Lean_Parser_hexnumNoAntiquot;
static lean_object* l_Lean_Parser_hexnum___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_hexnum;
static const lean_ctor_object l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_hexnum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 234, 249, 199, 49, 244, 72, 166)}};
static const lean_object* l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value;
static const lean_string_object l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 385, .m_capacity = 385, .m_length = 384, .m_data = "The parser `hexnum` parses a hexadecimal numeric literal not containing the `0x` prefix.\n\nIt produces a `hexnumKind` node containing an atom with the text of the\nliteral. This parser is mainly used for creating atoms such `#<hexnum>`. Recall that `hexnum`\nis not a token and this parser must be prefixed by another parser.\n\nFor numerals such as `0xadef100a`, you should use `numLit`.\n"};
static const lean_object* l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_scientificLit_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l_Lean_Parser_scientificLit_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_scientificLit_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_scientificLit_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_scientificLit_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l_Lean_Parser_scientificLit_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_scientificLit_formatter___closed__1_value;
static lean_object* l_Lean_Parser_scientificLit_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_scientificLit_parenthesizer___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_scientificLit___closed__0;
extern lean_object* l_Lean_Parser_scientificLitNoAntiquot;
static lean_object* l_Lean_Parser_scientificLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit;
static const lean_string_object l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "scientificLit"};
static const lean_object* l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 25, 249, 160, 8, 56, 13, 159)}};
static const lean_object* l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 287, .m_capacity = 287, .m_length = 286, .m_data = "The parser `scientific` parses a scientific-notation literal, such as `1.3e-24`.\n\nThis parser has arity 1: it produces a `scientificLitKind` node containing an atom with the text\nof the literal.\nYou can use `TSyntax.getScientific` to extract the parts from the resulting syntax object. "};
static const lean_object* l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_strLit_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Parser_strLit_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_strLit_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_strLit_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_strLit_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Parser_strLit_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_strLit_formatter___closed__1_value;
static lean_object* l_Lean_Parser_strLit_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_strLit_parenthesizer___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_strLit___closed__0;
extern lean_object* l_Lean_Parser_strLitNoAntiquot;
static lean_object* l_Lean_Parser_strLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_strLit;
static const lean_string_object l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strLit"};
static const lean_object* l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 157, 94, 66, 135, 29, 115, 44)}};
static const lean_object* l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 494, .m_capacity = 494, .m_length = 491, .m_data = "The parser `str` parses a string literal, such as `\"foo\"` or `\"\\r\\n\"`. Strings can contain\nC-style escapes like `\\n`, `\\\"`, `\\x00` or `\\u2665`, as well as literal unicode characters like `∈`.\nNewlines in a string are interpreted literally.\n\nThis parser has arity 1: it produces a `strLitKind` node containing an atom with the raw\nliteral (including the quote marks and without interpreting the escapes).\nYou can use `TSyntax.getString` to decode the string from the resulting syntax object. "};
static const lean_object* l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_charLit_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l_Lean_Parser_charLit_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_charLit_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_charLit_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_charLit_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l_Lean_Parser_charLit_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_charLit_formatter___closed__1_value;
static lean_object* l_Lean_Parser_charLit_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLit_parenthesizer___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLit___closed__0;
extern lean_object* l_Lean_Parser_charLitNoAntiquot;
static lean_object* l_Lean_Parser_charLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_charLit;
static const lean_string_object l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "charLit"};
static const lean_object* l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 82, 20, 217, 44, 105, 253, 153)}};
static const lean_object* l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 604, .m_capacity = 604, .m_length = 595, .m_data = "The parser `char` parses a character literal, such as `'a'` or `'\\n'`. Character literals can\ncontain C-style escapes like `\\n`, `\\\"`, `\\x00` or `\\u2665`, as well as literal unicode characters\nlike `∈`, but must evaluate to a single unicode codepoint, so `'♥'` is allowed but `'❤️'` is not\n(since it is two codepoints but one grapheme cluster).\n\nThis parser has arity 1: it produces a `charLitKind` node containing an atom with the raw\nliteral (including the quote marks and without interpreting the escapes).\nYou can use `TSyntax.getChar` to decode the string from the resulting syntax object. "};
static const lean_object* l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_nameLit_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Parser_nameLit_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_nameLit_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_nameLit_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_nameLit_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_Parser_nameLit_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_nameLit_formatter___closed__1_value;
static lean_object* l_Lean_Parser_nameLit_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nameLit_parenthesizer___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nameLit___closed__0;
extern lean_object* l_Lean_Parser_nameLitNoAntiquot;
static lean_object* l_Lean_Parser_nameLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit;
static const lean_string_object l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nameLit"};
static const lean_object* l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 229, 203, 158, 195, 74, 86, 122)}};
static const lean_object* l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 340, .m_capacity = 340, .m_length = 339, .m_data = "The parser `name` parses a name literal like `` `foo``. The syntax is the same as for identifiers\n(see `ident`) but with a leading backquote.\n\nThis parser has arity 1: it produces a `nameLitKind` node containing the raw literal\n(including the backquote).\nYou can use `TSyntax.getName` to extract the name from the resulting syntax object. "};
static const lean_object* l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_group_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Parser_group_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_group_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_group_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_group_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Parser_group_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_group_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_group_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_group_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_group_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_group_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_group(lean_object*);
static const lean_ctor_object l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_group_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 0, 118, 179, 21, 142, 182, 74)}};
static const lean_object* l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value;
static const lean_string_object l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 323, .m_capacity = 323, .m_length = 322, .m_data = "The parser `group(p)` parses the same thing as `p`, but it wraps the results in a `groupKind`\nnode.\n\nThis parser always has arity 1, even if `p` does not. Parsers like `p*` are automatically\nrewritten to `group(p)*` if `p` does not have arity 1, so that the results from separate invocations\nof `p` can be differentiated. "};
static const lean_object* l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_many1Indent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "irrelevant"};
static const lean_object* l_Lean_Parser_many1Indent___closed__0 = (const lean_object*)&l_Lean_Parser_many1Indent___closed__0_value;
lean_object* l_Lean_Parser_checkColGe(lean_object*);
static lean_object* l_Lean_Parser_many1Indent___closed__1;
lean_object* l_Lean_Parser_withPosition(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent(lean_object*);
static const lean_string_object l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "many1Indent"};
static const lean_object* l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 214, 77, 50, 137, 69, 220, 172)}};
static const lean_object* l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 343, .m_capacity = 343, .m_length = 342, .m_data = "The parser `many1Indent(p)` is equivalent to `withPosition((colGe p)+)`. This has the effect of\nparsing one or more occurrences of `p`, where each subsequent `p` parse needs to be indented\nthe same or more than the first parse.\n\nThis parser has arity 1, and returns a list of the results from `p`.\n`p` is \"auto-grouped\" if it is not arity 1. "};
static const lean_object* l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent(lean_object*);
static const lean_string_object l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "manyIndent"};
static const lean_object* l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 71, 18, 147, 220, 40, 152, 21)}};
static const lean_object* l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 343, .m_capacity = 343, .m_length = 342, .m_data = "The parser `manyIndent(p)` is equivalent to `withPosition((colGe p)*)`. This has the effect of\nparsing zero or more occurrences of `p`, where each subsequent `p` parse needs to be indented\nthe same or more than the first parse.\n\nThis parser has arity 1, and returns a list of the results from `p`.\n`p` is \"auto-grouped\" if it is not arity 1. "};
static const lean_object* l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___boxed(lean_object*);
lean_object* l_Lean_Parser_checkColEq(lean_object*);
static lean_object* l_Lean_Parser_sepByIndent___closed__0;
static const lean_string_object l_Lean_Parser_sepByIndent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "line break"};
static const lean_object* l_Lean_Parser_sepByIndent___closed__1 = (const lean_object*)&l_Lean_Parser_sepByIndent___closed__1_value;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
static lean_object* l_Lean_Parser_sepByIndent___closed__2;
extern lean_object* l_Lean_Parser_pushNone;
static lean_object* l_Lean_Parser_sepByIndent___closed__3;
static lean_object* l_Lean_Parser_sepByIndent___closed__4;
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__0_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_backtrackExceptionId;
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign___redArg(uint8_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_sepByIndent_parenthesizer___closed__0;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_sepByIndent_parenthesizer___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol(lean_object*);
static const lean_string_object l_Lean_Parser_patternIgnore_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "patternIgnore"};
static const lean_object* l_Lean_Parser_patternIgnore_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_patternIgnore_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_patternIgnore_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_patternIgnore_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 83, 213, 191, 208, 4, 123, 240)}};
static const lean_object* l_Lean_Parser_patternIgnore_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_patternIgnore_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore(lean_object*);
static const lean_ctor_object l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_patternIgnore_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 215, 73, 33, 82, 129, 241, 190)}};
static const lean_object* l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value;
static const lean_string_object l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "No-op parser combinator that annotates subtrees to be ignored in syntax patterns. "};
static const lean_object* l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___boxed(lean_object*);
extern lean_object* l_Lean_Parser_skip;
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace;
static const lean_string_object l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ppHardSpace"};
static const lean_object* l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 124, 7, 8, 102, 65, 59, 148)}};
static const lean_object* l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "No-op parser that advises the pretty printer to emit a non-breaking space. "};
static const lean_object* l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace;
static const lean_string_object l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 171, 103, 94, 255, 150, 197, 120)}};
static const lean_object* l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "No-op parser that advises the pretty printer to emit a space/soft line break. "};
static const lean_object* l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine;
static const lean_string_object l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 204, 69, 5, 170, 223, 165)}};
static const lean_object* l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "No-op parser that advises the pretty printer to emit a hard line break. "};
static const lean_object* l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ppRealFill"};
static const lean_object* l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 4, 104, 76, 91, 82, 68, 154)}};
static const lean_object* l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "No-op parser combinator that advises the pretty printer to emit a `Format.fill` node. "};
static const lean_object* l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ppRealGroup"};
static const lean_object* l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 63, 239, 92, 165, 98, 92, 199)}};
static const lean_object* l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "No-op parser combinator that advises the pretty printer to emit a `Format.group` node. "};
static const lean_object* l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppIndent"};
static const lean_object* l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 194, 209, 68, 183, 68, 71, 156)}};
static const lean_object* l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 105, .m_capacity = 105, .m_length = 104, .m_data = "No-op parser combinator that advises the pretty printer to indent the given syntax without grouping it. "};
static const lean_object* l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppGroup"};
static const lean_object* l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 202, 60, 40, 216, 102, 169, 77)}};
static const lean_object* l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 143, .m_capacity = 143, .m_length = 142, .m_data = "No-op parser combinator that advises the pretty printer to group and indent the given syntax.\nBy default, only syntax categories are grouped. "};
static const lean_object* l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppDedent"};
static const lean_object* l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 177, 202, 50, 99, 27, 117, 200)}};
static const lean_object* l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "No-op parser combinator that advises the pretty printer to dedent the given syntax.\nDedenting can in particular be used to counteract automatic indentation. "};
static const lean_object* l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped;
static const lean_string_object l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ppAllowUngrouped"};
static const lean_object* l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 185, 47, 125, 165, 106, 223, 132)}};
static const lean_object* l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 277, .m_capacity = 277, .m_length = 276, .m_data = "No-op parser combinator that allows the pretty printer to omit the group and\nindent operation in the enclosing category parser.\n```\nsyntax ppAllowUngrouped \"by \" tacticSeq : term\n-- allows a `by` after `:=` without linebreak in between:\ntheorem foo : True := by\n  trivial\n```\n"};
static const lean_object* l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ppDedentIfGrouped"};
static const lean_object* l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 220, 243, 72, 104, 9, 120, 214)}};
static const lean_object* l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 200, .m_capacity = 200, .m_length = 199, .m_data = "No-op parser combinator that advises the pretty printer to dedent the given syntax,\nif it was grouped by the category parser.\nDedenting can in particular be used to counteract automatic indentation. "};
static const lean_object* l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped;
static const lean_string_object l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ppHardLineUnlessUngrouped"};
static const lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 140, 119, 130, 113, 89, 214, 6)}};
static const lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "No-op parser combinator that prints a line break.\nThe line break is soft if the combinator is followed\nby an ungrouped parser (see ppAllowUngrouped), otherwise hard. "};
static const lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_ppHardSpace_formatter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_ppHardSpace_formatter___redArg___closed__0 = (const lean_object*)&l_Lean_ppHardSpace_formatter___redArg___closed__0_value;
static const lean_ctor_object l_Lean_ppHardSpace_formatter___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_ppHardSpace_formatter___redArg___closed__0_value)}};
static const lean_object* l_Lean_ppHardSpace_formatter___redArg___closed__1 = (const lean_object*)&l_Lean_ppHardSpace_formatter___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_fill(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppRealFill_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppRealFill_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_group(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppRealGroup_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppRealGroup_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_indent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppIndent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_ppDedent_formatter___closed__0;
lean_object* l_Std_Format_getIndent(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppDedent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppDedent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppDedentIfGrouped_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppDedentIfGrouped_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "termRegister_parser_alias(Kind:=_)______"};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__0 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__0_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value_aux_0),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 135, 36, 196, 99, 128, 246, 50)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value;
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__2 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__2_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value;
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "register_parser_alias "};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__4 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__4_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__4_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__5 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__5_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__6 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__6_value;
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__7 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__7_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__8 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__8_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__6_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__8_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__9 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__9_value;
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__10 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__10_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__10_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__11 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__11_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__9_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__11_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__12 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__12_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_termParser_formatter___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__12_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__14 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__14_value;
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ") "};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__15 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__15_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__15_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__16 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__16_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__14_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__16_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__17 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__17_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_group_formatter___closed__1_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__17_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__18 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__18_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_optional_formatter___closed__1_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__18_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__19 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__19_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__5_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__19_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__20 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__20_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_strLit_formatter___closed__1_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__21 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__21_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__21_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__24 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__24_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_optional_formatter___closed__1_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__24_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__25 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__25_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__20_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__25_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__26 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__26_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_ident_formatter___closed__1_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__27 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__27_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__26_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__27_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__28 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__28_value;
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGt"};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__29 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__29_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__29_value),LEAN_SCALAR_PTR_LITERAL(185, 236, 32, 153, 169, 213, 53, 244)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__30 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__30_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__30_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__31 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__31_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__31_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__32 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__32_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__32_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__33 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__33_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_optional_formatter___closed__1_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__33_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__34 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__34_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__28_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__34_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__35 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__35_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__35_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__36 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__36_value;
LEAN_EXPORT const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29____________ = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__36_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "expected non-overloaded constant name"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__0 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__0_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "PrettyPrinter.Formatter.registerAlias"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__2 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__2_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__4 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__4_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Formatter"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__5 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__5_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2_value),LEAN_SCALAR_PTR_LITERAL(126, 243, 114, 121, 141, 142, 42, 100)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__6 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__6_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "PrettyPrinter.Parenthesizer.registerAlias"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__7 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__7_value;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Parenthesizer"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__9 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__9_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 187, 150, 116, 216, 103, 117, 60)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__10 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__10_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__11 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__11_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "kind\?"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12_value;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(234, 251, 71, 75, 78, 98, 206, 187)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__14 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__14_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__15 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__15_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16_value;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(37, 202, 7, 33, 103, 74, 114, 212)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__18 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__18_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__19 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__19_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Parser.registerAlias"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "registerAlias"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(46, 201, 23, 171, 41, 77, 220, 95)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(212, 182, 194, 13, 246, 198, 212, 204)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(81, 39, 139, 251, 9, 82, 71, 189)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doubleQuotedName"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(194, 121, 78, 150, 98, 156, 35, 157)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39_value;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term{}"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_value),LEAN_SCALAR_PTR_LITERAL(44, 141, 217, 101, 193, 131, 35, 71)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__44 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__44_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__45 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__45_value;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47_value;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_value;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value_aux_0),((lean_object*)&l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58;
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60;
lean_object* l_Lean_Macro_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__1_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__1_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__1_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
lean_object* l_Lean_PrettyPrinter_Formatter_fill___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_fill___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
lean_object* l_Lean_PrettyPrinter_Formatter_group___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__4_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_group___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__4_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__4_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__6_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extra_0__Lean_initFn___lam__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_patternIgnore_formatter___closed__1_value)} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__6_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__6_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__7_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 165, 69, 201, 179, 176, 38, 97)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__7_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__7_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__8_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__8_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__8_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__11_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 56, 209, 55, 154, 125, 240, 2)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__11_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__11_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__12_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__12_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__12_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__14_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 164, 225, 181, 149, 187, 81, 113)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__14_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__14_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__1_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__16_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__16_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__16_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__17_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ppDedentIfGrouped_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__17_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__17_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__18_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__17_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__18_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__18_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__20_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 37, 230, 124, 106, 100, 159, 37)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__20_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__20_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__21_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__21_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__21_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__22_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ppDedent_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__22_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__22_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__23_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__22_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__23_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__23_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__24_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 142, 232, 190, 100, 212, 29, 41)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__24_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__24_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__25_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__25_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__25_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__26_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ppIndent_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__26_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__26_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__27_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__26_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__27_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__27_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__28_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 219, 143, 167, 248, 5, 230, 49)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__28_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__28_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__29_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__29_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__29_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__30_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__30_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__30_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__31_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 184, 190, 137, 27, 87, 63, 174)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__31_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__31_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__32_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__32_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__32_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__33_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__4_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__33_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__33_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__34_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__6_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__34_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__34_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__35_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__35_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__35_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__36_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 180, 65, 169, 196, 28, 141, 221)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__36_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__36_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__37_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__37_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__37_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__38_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__38_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__38_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__39_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ppGroup_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__39_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__39_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__40_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__39_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__40_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__40_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__41_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__41_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__41_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__42_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__42_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__42_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__44_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__44_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__44_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__45_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__45_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__45_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__46_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 168, 190, 83, 177, 86, 113, 221)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__46_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__46_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__48_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__48_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__48_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__49_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__49_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__49_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__50_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__49_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__50_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__50_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__52_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__52_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__52_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__53_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__52_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__53_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__53_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__54_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extra_0__Lean_initFn___lam__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_group_formatter___closed__1_value)} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__54_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__54_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__55_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__54_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__55_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__55_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__56_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__56_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__56_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__57_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_group_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__57_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__57_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__58_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__57_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__58_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__58_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__59_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_group_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__59_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__59_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__60_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__59_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__60_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__60_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__61_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_patternIgnore_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__61_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__61_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__62_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__61_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__62_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__62_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__63_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_patternIgnore_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__63_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__63_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__64_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__63_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__64_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__64_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
lean_object* l_Lean_Parser_registerAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed), 5, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed), 5, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_8, x_11, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_leadingNode_formatter___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_leadingNode_formatter___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_leadingNode_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = ((lean_object*)(l_Lean_Parser_termParser_formatter___redArg___closed__1));
x_7 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_termParser_formatter___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_termParser_formatter___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_termParser_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = ((lean_object*)(l_Lean_Parser_termParser_formatter___redArg___closed__1));
x_8 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_termParser_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = ((lean_object*)(l_Lean_Parser_commandParser_formatter___redArg___closed__1));
x_7 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_commandParser_formatter___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_commandParser_formatter___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_commandParser_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = ((lean_object*)(l_Lean_Parser_commandParser_formatter___redArg___closed__1));
x_8 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_commandParser_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_atomic_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_setExpected_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_setExpected_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_symbol_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_adaptCacheableContext_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_adaptCacheableContext_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_decQuotDepth_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__2));
x_7 = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__8));
x_8 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_antiquotNestedExpr_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__2));
x_4 = ((lean_object*)(l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_formatter___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_formatter___boxed), 5, 0);
x_2 = ((lean_object*)(l_Lean_Parser_antiquotExpr_formatter___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed), 5, 0);
x_7 = l_Lean_Parser_antiquotExpr_formatter___closed__2;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_antiquotExpr_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_nonReservedSymbol_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_nonReservedSymbol_formatter___redArg(x_1, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Parser_nonReservedSymbol_formatter(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_mkAntiquot_formatter___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_4);
x_10 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1));
x_11 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3));
x_12 = lean_box(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_10, x_15, x_5, x_6, x_7, x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1));
x_18 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3));
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_22, 0, x_18);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(x_24, 0, x_17);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed), 5, 0);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_4);
x_27 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_24, x_26, x_5, x_6, x_7, x_8);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Parser_mkAntiquot_formatter___lam__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_symbol_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_mkAntiquot_formatter___lam__2(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_mkAntiquot_formatter___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__0));
x_11 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__1));
x_12 = lean_box(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___boxed), 9, 4);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_11);
if (x_4 == 0)
{
lean_object* x_27; 
x_27 = lean_box(0);
x_14 = x_27;
goto block_26;
}
else
{
lean_object* x_28; 
x_28 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__10));
x_14 = x_28;
goto block_26;
}
block_26:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = l_Lean_Name_append(x_2, x_14);
x_16 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__3));
x_17 = l_Lean_Name_append(x_15, x_16);
x_18 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__5));
x_19 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__8));
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotExpr_formatter___boxed), 5, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_13);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_22, 0, x_10);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___lam__3___boxed), 7, 2);
lean_closure_set(x_24, 0, x_18);
lean_closure_set(x_24, 1, x_23);
x_25 = l_Lean_Parser_leadingNode_formatter___redArg(x_17, x_24, x_5, x_6, x_7, x_8);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Parser_mkAntiquot_formatter(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_setExpected_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_setExpected_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_symbol_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_adaptCacheableContext_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_decQuotDepth_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_termParser_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__2));
x_7 = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4));
x_8 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_antiquotNestedExpr_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__2));
x_4 = ((lean_object*)(l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_parenthesizer___boxed), 5, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_parenthesizer___boxed), 5, 0);
x_2 = ((lean_object*)(l_Lean_Parser_antiquotExpr_parenthesizer___closed__0));
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed), 5, 0);
x_7 = l_Lean_Parser_antiquotExpr_parenthesizer___closed__1;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_antiquotExpr_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(x_1, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(x_1, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Parser_nonReservedSymbol_parenthesizer(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_symbol_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_mkAntiquot_parenthesizer___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_4);
x_10 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1));
x_11 = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0));
x_12 = lean_box(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_10, x_15, x_5, x_6, x_7, x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1));
x_18 = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0));
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_22, 0, x_18);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed), 7, 2);
lean_closure_set(x_24, 0, x_17);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed), 5, 0);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_4);
x_27 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_24, x_26, x_5, x_6, x_7, x_8);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Parser_mkAntiquot_parenthesizer___lam__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_mkAntiquot_parenthesizer___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___closed__2));
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___closed__0));
if (x_4 == 0)
{
lean_object* x_28; 
x_28 = lean_box(0);
x_11 = x_28;
goto block_27;
}
else
{
lean_object* x_29; 
x_29 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__10));
x_11 = x_29;
goto block_27;
}
block_27:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = l_Lean_Name_append(x_2, x_11);
x_13 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__3));
x_14 = l_Lean_Name_append(x_12, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___closed__1));
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
x_18 = lean_box(x_3);
lean_inc_ref(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___boxed), 9, 4);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_17);
lean_closure_set(x_19, 3, x_10);
x_20 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__4;
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotExpr_parenthesizer___boxed), 5, 0);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_19);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_24, 0, x_20);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed), 7, 2);
lean_closure_set(x_25, 0, x_16);
lean_closure_set(x_25, 1, x_24);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(x_14, x_15, x_25, x_5, x_6, x_7, x_8);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Parser_mkAntiquot_parenthesizer(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = 0;
x_11 = lean_box(x_4);
x_12 = lean_box(x_10);
lean_inc(x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
x_15 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_14, x_5, x_6, x_7, x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Parser_nodeWithAntiquot_formatter(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = 0;
x_11 = lean_box(x_4);
x_12 = lean_box(x_10);
lean_inc(x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed), 7, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_14, x_5, x_6, x_7, x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Parser_nodeWithAntiquot_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__0));
x_10 = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__1));
x_11 = l_Lean_Name_append(x_1, x_10);
x_12 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__5));
x_13 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__8));
x_14 = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__3));
x_15 = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__5));
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_2);
x_17 = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__7));
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_3);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_20, 0, x_14);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_21, 0, x_9);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_22, 0, x_13);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___lam__3___boxed), 7, 2);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_22);
x_24 = l_Lean_Parser_leadingNode_formatter___redArg(x_11, x_23, x_4, x_5, x_6, x_7);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_mkAntiquotSplice_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0___boxed), 6, 1);
lean_closure_set(x_9, 0, x_2);
lean_inc_ref(x_3);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquotSplice_formatter___boxed), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___boxed), 8, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
x_12 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_10, x_11, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_string_utf8_byte_size(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_String_Slice_trimAscii(x_10);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__1));
x_16 = lean_string_utf8_extract(x_12, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_17 = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__2));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter___boxed), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(x_15, x_1, x_19, x_3, x_4, x_5, x_6);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_sepByElemParser_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_formatter___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_sepBy_formatter___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_sepBy_formatter___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Parser_sepBy_formatter(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__1));
x_10 = l_Lean_Name_append(x_1, x_9);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___closed__1));
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
x_14 = l_Lean_Parser_mkAntiquot_parenthesizer___closed__4;
x_15 = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__0));
x_16 = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__5));
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed), 7, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_2);
x_18 = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1));
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_3);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_21, 0, x_15);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_22, 0, x_13);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_23, 0, x_14);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed), 7, 2);
lean_closure_set(x_24, 0, x_12);
lean_closure_set(x_24, 1, x_23);
x_25 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(x_10, x_11, x_24, x_4, x_5, x_6, x_7);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_mkAntiquotSplice_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(x_9, 0, x_2);
lean_inc_ref(x_3);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquotSplice_parenthesizer___boxed), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed), 8, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_10, x_11, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_string_utf8_byte_size(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_String_Slice_trimAscii(x_10);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__1));
x_16 = lean_string_utf8_extract(x_12, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_17 = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__2));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(x_15, x_1, x_19, x_3, x_4, x_5, x_6);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_sepByElemParser_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_parenthesizer___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_sepBy_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_sepBy_parenthesizer___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Parser_sepBy_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_formatter___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_sepBy1_formatter___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_sepBy1_formatter___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Parser_sepBy1_formatter(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_parenthesizer___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_sepBy1_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_sepBy1_parenthesizer___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Parser_sepBy1_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_formatter(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___boxed), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_9);
x_11 = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Parser_unicodeSymbol_formatter(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_9);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Parser_unicodeSymbol_parenthesizer(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withCache_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_withCache_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withCache_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_withCache_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withResetCache_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withResetCache_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withPosition_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withPositionAfterLinebreak_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withoutPosition_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withoutPosition_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withForbidden_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_withForbidden_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withForbidden_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_withForbidden_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withoutForbidden_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withoutForbidden_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_incQuotDepth_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_incQuotDepth_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_suppressInsideQuot_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_suppressInsideQuot_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_evalInsideQuot_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_evalInsideQuot_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_evalInsideQuot_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_evalInsideQuot_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withOpen_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withOpen_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withOpenDecl_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_withOpenDecl_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_dbgTraceState_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_dbgTraceState_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_dbgTraceState_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_dbgTraceState_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optional_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = ((lean_object*)(l_Lean_Parser_optional_formatter___closed__1));
x_8 = ((lean_object*)(l_Lean_Parser_optional_formatter___closed__3));
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter(x_9, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_optional_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optional_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = ((lean_object*)(l_Lean_Parser_optional_formatter___closed__1));
x_8 = ((lean_object*)(l_Lean_Parser_optional_parenthesizer___closed__0));
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_9, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_optional_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_optional___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_optional_formatter___closed__2));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optional(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Parser_optional_formatter___closed__1));
x_3 = l_Lean_Parser_optional___closed__0;
x_4 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_2, x_1, x_3);
x_5 = l_Lean_Parser_optionalNoAntiquot(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0));
x_3 = ((lean_object*)(l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__1));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = ((lean_object*)(l_Lean_Parser_many_formatter___closed__1));
x_8 = ((lean_object*)(l_Lean_Parser_many_formatter___closed__2));
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(x_9, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_many_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = ((lean_object*)(l_Lean_Parser_many_formatter___closed__1));
x_8 = ((lean_object*)(l_Lean_Parser_many_parenthesizer___closed__0));
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(x_9, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_many_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_many___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__2));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Parser_many_formatter___closed__1));
x_3 = l_Lean_Parser_many___closed__0;
x_4 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_2, x_1, x_3);
x_5 = l_Lean_Parser_manyNoAntiquot(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0));
x_3 = ((lean_object*)(l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__1));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = ((lean_object*)(l_Lean_Parser_many_formatter___closed__1));
x_8 = ((lean_object*)(l_Lean_Parser_many_formatter___closed__2));
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(x_9, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_many1_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = ((lean_object*)(l_Lean_Parser_many_formatter___closed__1));
x_8 = ((lean_object*)(l_Lean_Parser_many_parenthesizer___closed__0));
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(x_9, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_many1_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Parser_many_formatter___closed__1));
x_3 = l_Lean_Parser_many___closed__0;
x_4 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_2, x_1, x_3);
x_5 = l_Lean_Parser_many1NoAntiquot(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ident_formatter___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_ident_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_ident_formatter___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ident_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_ident_formatter___closed__2;
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed), 5, 0);
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ident_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ident_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_ident_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_ident_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_ident_formatter___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ident_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_ident_parenthesizer___closed__0;
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed), 5, 0);
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ident_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ident_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_ident___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_ident_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_ident_formatter___closed__0));
x_5 = l_Lean_Parser_mkAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_ident___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_identNoAntiquot;
x_2 = l_Lean_Parser_ident___closed__0;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_ident() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_ident___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0));
x_3 = ((lean_object*)(l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__1));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter___boxed), 5, 0);
x_2 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__0));
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2;
x_2 = ((lean_object*)(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3;
x_2 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__0));
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter___boxed), 5, 0);
x_7 = l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5;
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_identWithPartialTrailingDot_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1;
x_2 = ((lean_object*)(l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__0));
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer___boxed), 5, 0);
x_7 = l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_identWithPartialTrailingDot_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_identWithPartialTrailingDot___closed__0));
x_2 = l_Lean_Parser_checkNoWsBefore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0));
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_ident;
x_2 = l_Lean_Parser_identWithPartialTrailingDot___closed__1;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_identWithPartialTrailingDot___closed__3;
x_2 = l_Lean_Parser_identWithPartialTrailingDot___closed__2;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_identWithPartialTrailingDot___closed__4;
x_2 = l_Lean_Parser_identWithPartialTrailingDot___closed__1;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_identWithPartialTrailingDot___closed__5;
x_2 = l_Lean_Parser_optional(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_identWithPartialTrailingDot___closed__6;
x_2 = l_Lean_Parser_ident;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_identWithPartialTrailingDot___closed__7;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_ident_formatter___closed__2;
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter___boxed), 5, 0);
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_rawIdent_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_rawIdent_parenthesizer___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_Parser_rawIdent_parenthesizer___closed__0));
x_7 = l_Lean_Parser_ident_parenthesizer___closed__0;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_7, x_6, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_rawIdent_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_rawIdent___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_rawIdentNoAntiquot;
x_2 = l_Lean_Parser_ident___closed__0;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_rawIdent() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_rawIdent___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfo_formatter___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lean_Parser_hygieneInfo_formatter___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_hygieneInfo_formatter___closed__0));
x_4 = lean_box(x_1);
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__1));
x_7 = l_Lean_Parser_hygieneInfo_formatter___closed__2;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_7, x_6, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_hygieneInfo_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfo_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lean_Parser_hygieneInfo_formatter___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_hygieneInfo_formatter___closed__0));
x_4 = lean_box(x_1);
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___closed__0));
x_7 = l_Lean_Parser_hygieneInfo_parenthesizer___closed__0;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_7, x_6, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_hygieneInfo_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfo___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lean_Parser_hygieneInfo_formatter___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_hygieneInfo_formatter___closed__0));
x_4 = l_Lean_Parser_mkAntiquot(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_hygieneInfoNoAntiquot;
x_2 = l_Lean_Parser_hygieneInfo___closed__0;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_hygieneInfo___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0));
x_3 = ((lean_object*)(l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__1));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_numLit_formatter___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_numLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_numLit_formatter___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_numLit_formatter___closed__2;
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___boxed), 5, 0);
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_numLit_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_numLit_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_numLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_numLit_formatter___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_Parser_rawIdent_parenthesizer___closed__0));
x_7 = l_Lean_Parser_numLit_parenthesizer___closed__0;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_7, x_6, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_numLit_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_numLit___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_numLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_numLit_formatter___closed__0));
x_5 = l_Lean_Parser_mkAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_numLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_numLitNoAntiquot;
x_2 = l_Lean_Parser_numLit___closed__0;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_numLit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_numLit___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_hexnum___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_hexnum___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_hexnum___closed__0));
x_5 = l_Lean_Parser_mkAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_hexnum___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_hexnumNoAntiquot;
x_2 = l_Lean_Parser_hexnum___closed__2;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_hexnum() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_hexnum___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0));
x_3 = ((lean_object*)(l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__1));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit_formatter___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_scientificLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_scientificLit_formatter___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_scientificLit_formatter___closed__2;
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___boxed), 5, 0);
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_scientificLit_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_scientificLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_scientificLit_formatter___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_Parser_rawIdent_parenthesizer___closed__0));
x_7 = l_Lean_Parser_scientificLit_parenthesizer___closed__0;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_7, x_6, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_scientificLit_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_scientificLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_scientificLit_formatter___closed__0));
x_5 = l_Lean_Parser_mkAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_scientificLitNoAntiquot;
x_2 = l_Lean_Parser_scientificLit___closed__0;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_scientificLit___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_strLit_formatter___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_strLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_strLit_formatter___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_strLit_formatter___closed__2;
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___boxed), 5, 0);
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strLit_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_strLit_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_strLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_strLit_formatter___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_Parser_rawIdent_parenthesizer___closed__0));
x_7 = l_Lean_Parser_strLit_parenthesizer___closed__0;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_7, x_6, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strLit_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_strLit___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_strLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_strLit_formatter___closed__0));
x_5 = l_Lean_Parser_mkAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_strLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_strLitNoAntiquot;
x_2 = l_Lean_Parser_strLit___closed__0;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_strLit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_strLit___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_charLit_formatter___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_charLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_charLit_formatter___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_charLit_formatter___closed__2;
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___boxed), 5, 0);
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_charLit_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_charLit_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_charLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_charLit_formatter___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_Parser_rawIdent_parenthesizer___closed__0));
x_7 = l_Lean_Parser_charLit_parenthesizer___closed__0;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_7, x_6, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_charLit_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_charLit___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_charLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_charLit_formatter___closed__0));
x_5 = l_Lean_Parser_mkAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_charLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_charLitNoAntiquot;
x_2 = l_Lean_Parser_charLit___closed__0;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_charLit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_charLit___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_nameLit_formatter___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_nameLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_nameLit_formatter___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_nameLit_formatter___closed__2;
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___boxed), 5, 0);
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_nameLit_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_nameLit_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_nameLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_nameLit_formatter___closed__0));
x_5 = lean_box(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_Parser_rawIdent_parenthesizer___closed__0));
x_7 = l_Lean_Parser_nameLit_parenthesizer___closed__0;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_7, x_6, x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_nameLit_parenthesizer(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_nameLit___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = ((lean_object*)(l_Lean_Parser_nameLit_formatter___closed__1));
x_4 = ((lean_object*)(l_Lean_Parser_nameLit_formatter___closed__0));
x_5 = l_Lean_Parser_mkAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_nameLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_nameLitNoAntiquot;
x_2 = l_Lean_Parser_nameLit___closed__0;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_nameLit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_nameLit___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_group_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = ((lean_object*)(l_Lean_Parser_group_formatter___closed__1));
x_8 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_group_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_group_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_group_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = ((lean_object*)(l_Lean_Parser_group_formatter___closed__1));
x_8 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_group_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_group_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_group(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Parser_group_formatter___closed__1));
x_3 = l_Lean_Parser_node(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0));
x_3 = ((lean_object*)(l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__1));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 5, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_many1_formatter(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_many1Indent_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_many1_parenthesizer___boxed), 6, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(x_9, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_many1Indent_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_many1Indent___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_many1Indent___closed__0));
x_2 = l_Lean_Parser_checkColGe(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_many1Indent___closed__1;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
x_4 = l_Lean_Parser_many1(x_3);
x_5 = l_Lean_Parser_withPosition(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 5, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_many_formatter(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_manyIndent_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(x_9, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_manyIndent_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_many1Indent___closed__1;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
x_4 = l_Lean_Parser_many(x_3);
x_5 = l_Lean_Parser_withPosition(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_sepByIndent___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_many1Indent___closed__0));
x_2 = l_Lean_Parser_checkColEq(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_sepByIndent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Parser_sepByIndent___closed__1));
x_2 = l_Lean_Parser_checkLinebreakBefore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_sepByIndent___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_pushNone;
x_2 = l_Lean_Parser_sepByIndent___closed__2;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_sepByIndent___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_sepByIndent___closed__3;
x_2 = l_Lean_Parser_sepByIndent___closed__0;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__1));
x_6 = l_Lean_Parser_many___closed__0;
x_7 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_5, x_1, x_6);
x_8 = l_Lean_Parser_many1Indent___closed__1;
x_9 = l_Lean_Parser_andthen(x_8, x_7);
x_10 = l_Lean_Parser_sepByIndent___closed__4;
x_11 = l_Lean_Parser_orelse(x_3, x_10);
x_12 = l_Lean_Parser_sepBy(x_9, x_2, x_11, x_4);
x_13 = l_Lean_Parser_withPosition(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Parser_sepByIndent(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__1));
x_6 = l_Lean_Parser_many___closed__0;
x_7 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_5, x_1, x_6);
x_8 = l_Lean_Parser_many1Indent___closed__1;
x_9 = l_Lean_Parser_andthen(x_8, x_7);
x_10 = l_Lean_Parser_sepByIndent___closed__4;
x_11 = l_Lean_Parser_orelse(x_3, x_10);
x_12 = l_Lean_Parser_sepBy1(x_9, x_2, x_11, x_4);
x_13 = l_Lean_Parser_withPosition(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Parser_sepBy1Indent(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_take(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Syntax_Traverser_left(x_5);
lean_ctor_set(x_3, 0, x_6);
x_7 = lean_st_ref_set(x_1, x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_16 = l_Lean_Syntax_Traverser_left(x_10);
x_17 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 1, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 2, x_14);
x_18 = lean_st_ref_set(x_1, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_box(0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_mod(x_12, x_20);
x_22 = lean_nat_dec_eq(x_21, x_19);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_st_ref_get(x_7);
lean_inc_ref(x_1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_24 = lean_apply_5(x_1, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_24) == 0)
{
lean_dec_ref(x_24);
lean_dec(x_23);
x_4 = x_13;
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_38; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_38 = l_Lean_Exception_isInterrupt(x_26);
if (x_38 == 0)
{
uint8_t x_39; 
lean_inc(x_26);
x_39 = l_Lean_Exception_isRuntime(x_26);
x_28 = x_39;
goto block_37;
}
else
{
x_28 = x_38;
goto block_37;
}
block_37:
{
if (x_28 == 0)
{
if (lean_obj_tag(x_26) == 0)
{
lean_dec_ref(x_26);
lean_dec(x_23);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_24;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec_ref(x_26);
x_30 = l_Lean_instBEqInternalExceptionId_beq(x_27, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_dec(x_23);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec_ref(x_24);
x_31 = lean_st_ref_set(x_7, x_23);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_2, x_32);
x_34 = lean_nat_dec_eq(x_12, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1));
x_36 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(x_35, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_dec_ref(x_36);
x_15 = lean_box(0);
goto block_18;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_36;
}
}
else
{
x_15 = lean_box(0);
goto block_18;
}
}
}
}
else
{
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_24;
}
}
}
}
else
{
lean_object* x_40; 
lean_inc_ref(x_3);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_40 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_40) == 0)
{
lean_dec_ref(x_40);
x_4 = x_13;
x_5 = x_14;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_40;
}
}
block_18:
{
lean_object* x_16; 
x_16 = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(x_7);
lean_dec_ref(x_16);
x_4 = x_13;
x_5 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
}
else
{
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Parser_sepByIndent_formatter___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 1)
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_16; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_nat_mod(x_4, x_22);
x_24 = lean_nat_dec_eq(x_23, x_8);
lean_dec(x_23);
if (x_24 == 0)
{
x_16 = x_24;
goto block_21;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_array_fget_borrowed(x_2, x_4);
lean_inc(x_25);
x_26 = l_Lean_Syntax_matchesNull(x_25, x_6);
x_16 = x_26;
goto block_21;
}
block_15:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_12 = lean_box(x_10);
x_13 = lean_array_push(x_5, x_12);
x_3 = x_9;
x_4 = x_11;
x_5 = x_13;
goto _start;
}
block_21:
{
if (x_16 == 0)
{
x_10 = x_16;
goto block_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Lean_Syntax_getArgs(x_1);
x_18 = lean_array_get_size(x_17);
lean_dec_ref(x_17);
x_19 = lean_nat_sub(x_18, x_8);
x_20 = lean_nat_dec_eq(x_4, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
x_10 = x_16;
goto block_15;
}
else
{
x_10 = x_7;
goto block_15;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
lean_dec(x_5);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_Syntax_getArgs(x_9);
x_11 = lean_array_get_size(x_10);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_mk_empty_array_with_capacity(x_11);
x_26 = l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(x_9, x_10, x_11, x_24, x_25);
lean_dec_ref(x_10);
lean_dec(x_9);
x_27 = lean_array_get_size(x_26);
x_28 = lean_nat_dec_lt(x_24, x_27);
if (x_28 == 0)
{
lean_dec_ref(x_26);
x_12 = x_28;
goto block_23;
}
else
{
if (x_28 == 0)
{
lean_dec_ref(x_26);
x_12 = x_28;
goto block_23;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_27);
x_31 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4(x_26, x_29, x_30);
lean_dec_ref(x_26);
x_12 = x_31;
goto block_23;
}
}
block_23:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_List_range(x_11);
x_14 = l_List_reverse___redArg(x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_sepByIndent_formatter___redArg___lam__0___boxed), 10, 5);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_11);
lean_closure_set(x_16, 2, x_1);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_15);
lean_inc(x_4);
x_17 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_16, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
if (x_12 == 0)
{
lean_dec(x_4);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; 
lean_free_object(x_17);
x_20 = l_Lean_PrettyPrinter_Formatter_pushAlign___redArg(x_12, x_4);
lean_dec(x_4);
return x_20;
}
}
else
{
lean_dec(x_17);
if (x_12 == 0)
{
lean_object* x_21; 
lean_dec(x_4);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_15);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_PrettyPrinter_Formatter_pushAlign___redArg(x_12, x_4);
lean_dec(x_4);
return x_22;
}
}
}
else
{
lean_dec(x_4);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_sepByIndent_formatter___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_sepByIndent_formatter___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_sepByIndent_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapFinIdxM_map___at___00Lean_Parser_sepByIndent_formatter_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_sepByIndent_formatter___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_sepBy1Indent_formatter___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_sepByIndent_formatter___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_sepBy1Indent_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___closed__0));
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_sepByIndent_parenthesizer___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
x_11 = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__1));
x_12 = ((lean_object*)(l_Lean_Parser_many_parenthesizer___closed__0));
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_sepByIndent_parenthesizer___closed__1;
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_box(x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy_parenthesizer___boxed), 9, 4);
lean_closure_set(x_18, 0, x_14);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_16);
lean_closure_set(x_18, 3, x_17);
x_19 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(x_18, x_5, x_6, x_7, x_8);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Parser_sepByIndent_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
x_11 = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__1));
x_12 = ((lean_object*)(l_Lean_Parser_many_parenthesizer___closed__0));
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_sepByIndent_parenthesizer___closed__1;
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_box(x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(x_18, 0, x_14);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_16);
lean_closure_set(x_18, 3, x_17);
x_19 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(x_18, x_5, x_6, x_7, x_8);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Parser_sepBy1Indent_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___redArg() {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_notSymbol_formatter___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg();
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_notSymbol_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___redArg() {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_notSymbol_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg();
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_notSymbol_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
lean_inc_ref(x_1);
x_2 = l_Lean_Parser_symbol(x_1);
x_3 = l_Lean_Parser_notFollowedBy(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = ((lean_object*)(l_Lean_Parser_patternIgnore_formatter___closed__1));
x_8 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_patternIgnore_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = ((lean_object*)(l_Lean_Parser_patternIgnore_formatter___closed__1));
x_8 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_patternIgnore_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Parser_patternIgnore_formatter___closed__1));
x_3 = l_Lean_Parser_node(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0));
x_3 = ((lean_object*)(l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__1));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ppHardSpace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_skip;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ppSpace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_skip;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ppLine() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_skip;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppRealFill(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppRealGroup(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppIndent(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppGroup(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppDedent(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ppAllowUngrouped() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_skip;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppDedentIfGrouped(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ppHardLineUnlessUngrouped() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_skip;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__2));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l_Lean_ppHardSpace_formatter___redArg___closed__1));
x_4 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ppHardSpace_formatter___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppHardSpace_formatter___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppHardSpace_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ppSpace_formatter___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppSpace_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1));
x_4 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ppLine_formatter___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppLine_formatter___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppLine_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppRealFill_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_fill(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ppRealFill_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ppRealFill_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ppRealGroup_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_group(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ppRealGroup_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ppRealGroup_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ppIndent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_PrettyPrinter_Formatter_indent(x_1, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ppIndent_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ppIndent_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_ppDedent_formatter___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ppDedent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = l_Lean_ppDedent_formatter___closed__0;
x_9 = l_Std_Format_getIndent(x_7);
x_10 = lean_nat_to_int(x_9);
x_11 = lean_int_sub(x_8, x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_PrettyPrinter_Formatter_indent(x_1, x_12, x_2, x_3, x_4, x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_ppDedent_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ppDedent_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_take(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = 0;
lean_ctor_set_uint8(x_3, sizeof(void*)*3 + 2, x_5);
x_6 = lean_st_ref_set(x_1, x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_14 = 0;
x_15 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 2, x_14);
x_16 = lean_st_ref_set(x_1, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ppAllowUngrouped_formatter___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppAllowUngrouped_formatter___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppAllowUngrouped_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppDedentIfGrouped_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_4);
lean_inc(x_3);
x_7 = l_Lean_PrettyPrinter_Formatter_concat(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_8 = x_7;
} else {
 lean_dec_ref(x_7);
 x_8 = lean_box(0);
}
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_11 = lean_st_ref_take(x_3);
x_17 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_18);
x_19 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_20 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_21 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 2);
x_22 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_22);
x_23 = lean_box(0);
x_24 = lean_array_get_size(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
x_27 = lean_nat_dec_lt(x_26, x_24);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec_ref(x_22);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_4);
x_12 = x_23;
x_13 = x_11;
goto block_16;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_11, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_11, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_11, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_32);
lean_dec_ref(x_4);
x_33 = l_Std_Format_getIndent(x_32);
lean_dec_ref(x_32);
x_34 = lean_array_fget(x_22, x_26);
x_35 = lean_array_fset(x_22, x_26, x_23);
x_36 = l_Lean_ppDedent_formatter___closed__0;
x_37 = lean_nat_to_int(x_33);
x_38 = lean_int_sub(x_36, x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
x_40 = lean_array_fset(x_35, x_26, x_39);
lean_dec(x_26);
lean_ctor_set(x_11, 2, x_40);
x_12 = x_23;
x_13 = x_11;
goto block_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_11);
x_41 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_41);
lean_dec_ref(x_4);
x_42 = l_Std_Format_getIndent(x_41);
lean_dec_ref(x_41);
x_43 = lean_array_fget(x_22, x_26);
x_44 = lean_array_fset(x_22, x_26, x_23);
x_45 = l_Lean_ppDedent_formatter___closed__0;
x_46 = lean_nat_to_int(x_42);
x_47 = lean_int_sub(x_45, x_46);
lean_dec(x_46);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
x_49 = lean_array_fset(x_44, x_26, x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_50, 0, x_17);
lean_ctor_set(x_50, 1, x_18);
lean_ctor_set(x_50, 2, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 1, x_20);
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 2, x_21);
x_12 = x_23;
x_13 = x_50;
goto block_16;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_st_ref_set(x_3, x_13);
lean_dec(x_3);
if (lean_is_scalar(x_8)) {
 x_15 = lean_alloc_ctor(0, 1, 0);
} else {
 x_15 = x_8;
}
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_4);
lean_dec(x_3);
x_51 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_52 = lean_alloc_ctor(0, 1, 0);
} else {
 x_52 = x_8;
}
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
else
{
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppDedentIfGrouped_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ppDedentIfGrouped_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_ppLine_formatter___redArg(x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppHardLineUnlessUngrouped_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___redArg() {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppHardSpace_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ppHardSpace_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___redArg() {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppSpace_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ppSpace_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___redArg() {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppLine_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ppLine_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_ppIndent_formatter___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_fill(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_ppGroup_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_ppRealFill_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_ppIndent_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_ppGroup_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_ppRealGroup_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_ppDedent_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg() {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ppAllowUngrouped_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_ppDedentIfGrouped_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg() {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__2));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__7));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(0);
x_3 = l_Lean_SourceInfo_fromRef(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__45));
x_2 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47));
x_2 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48;
x_2 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46;
x_3 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__44));
x_4 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40;
x_5 = l_Lean_Syntax_node2(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1;
x_2 = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__5));
x_3 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52;
x_2 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54));
x_3 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40;
x_4 = l_Lean_Syntax_node1(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52;
x_2 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57));
x_3 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40;
x_4 = l_Lean_Syntax_node1(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48;
x_2 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58;
x_3 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55;
x_4 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52;
x_5 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46;
x_6 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51));
x_7 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40;
x_8 = l_Lean_Syntax_node6(x_7, x_6, x_5, x_4, x_3, x_2, x_4, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59;
x_2 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49;
x_3 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42));
x_4 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40;
x_5 = l_Lean_Syntax_node2(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_226; uint8_t x_227; 
x_9 = ((lean_object*)(l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0));
x_226 = ((lean_object*)(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1));
lean_inc(x_1);
x_227 = l_Lean_Syntax_isOfKind(x_1, x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_228 = lean_box(1);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_3);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_230 = lean_unsigned_to_nat(1u);
x_231 = l_Lean_Syntax_getArg(x_1, x_230);
x_232 = l_Lean_Syntax_isNone(x_231);
if (x_232 == 0)
{
uint8_t x_233; 
lean_inc(x_231);
x_233 = l_Lean_Syntax_matchesNull(x_231, x_230);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_231);
lean_dec_ref(x_2);
lean_dec(x_1);
x_234 = lean_box(1);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_3);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_236 = lean_unsigned_to_nat(0u);
x_237 = l_Lean_Syntax_getArg(x_231, x_236);
lean_dec(x_231);
x_238 = ((lean_object*)(l_Lean_Parser_group_formatter___closed__1));
lean_inc(x_237);
x_239 = l_Lean_Syntax_isOfKind(x_237, x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_237);
lean_dec_ref(x_2);
lean_dec(x_1);
x_240 = lean_box(1);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_3);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_unsigned_to_nat(3u);
x_243 = l_Lean_Syntax_getArg(x_237, x_242);
lean_dec(x_237);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
x_211 = x_244;
x_212 = x_2;
x_213 = x_3;
goto block_225;
}
}
}
else
{
lean_object* x_245; 
lean_dec(x_231);
x_245 = lean_box(0);
x_211 = x_245;
x_212 = x_2;
x_213 = x_3;
goto block_225;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__0));
x_7 = l_Lean_Macro_throwError___redArg(x_6, x_4, x_5);
lean_dec_ref(x_4);
return x_7;
}
block_83:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_inc(x_22);
lean_inc(x_11);
x_37 = l_Lean_Syntax_node1(x_11, x_22, x_36);
lean_inc(x_21);
lean_inc(x_11);
x_38 = l_Lean_Syntax_node2(x_11, x_21, x_18, x_37);
x_39 = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__5));
lean_inc(x_11);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_11);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_11);
x_41 = l_Lean_Syntax_node5(x_11, x_31, x_25, x_24, x_13, x_38, x_40);
lean_inc(x_26);
lean_inc(x_27);
lean_inc(x_22);
lean_inc(x_11);
x_42 = l_Lean_Syntax_node5(x_11, x_22, x_27, x_34, x_26, x_14, x_41);
lean_inc(x_21);
lean_inc(x_11);
x_43 = l_Lean_Syntax_node2(x_11, x_21, x_19, x_42);
lean_inc(x_23);
lean_inc(x_11);
x_44 = l_Lean_Syntax_node1(x_11, x_23, x_43);
x_45 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1;
lean_inc(x_22);
lean_inc(x_11);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_11);
lean_ctor_set(x_46, 1, x_22);
lean_ctor_set(x_46, 2, x_45);
lean_inc_ref(x_46);
lean_inc(x_32);
lean_inc(x_11);
x_47 = l_Lean_Syntax_node2(x_11, x_32, x_44, x_46);
x_48 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3;
x_49 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__4));
x_50 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__5));
lean_inc_ref(x_33);
x_51 = l_Lean_Name_mkStr3(x_49, x_50, x_33);
lean_inc(x_35);
lean_inc(x_12);
x_52 = l_Lean_addMacroScope(x_12, x_51, x_35);
lean_inc_ref(x_33);
x_53 = l_Lean_Name_mkStr4(x_9, x_49, x_50, x_33);
lean_inc(x_10);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_10);
lean_inc(x_29);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_29);
lean_inc(x_11);
x_56 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_56, 0, x_11);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_52);
lean_ctor_set(x_56, 3, x_55);
x_57 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__6));
lean_inc(x_28);
x_58 = l_Lean_Name_append(x_28, x_57);
x_59 = l_Lean_mkIdentFrom(x_26, x_58, x_20);
lean_inc(x_27);
lean_inc(x_22);
lean_inc(x_11);
x_60 = l_Lean_Syntax_node2(x_11, x_22, x_27, x_59);
lean_inc(x_21);
lean_inc(x_11);
x_61 = l_Lean_Syntax_node2(x_11, x_21, x_56, x_60);
lean_inc(x_23);
lean_inc(x_11);
x_62 = l_Lean_Syntax_node1(x_11, x_23, x_61);
lean_inc_ref(x_46);
lean_inc(x_32);
lean_inc(x_11);
x_63 = l_Lean_Syntax_node2(x_11, x_32, x_62, x_46);
x_64 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8;
x_65 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__9));
lean_inc_ref(x_33);
x_66 = l_Lean_Name_mkStr3(x_49, x_65, x_33);
x_67 = l_Lean_addMacroScope(x_12, x_66, x_35);
x_68 = l_Lean_Name_mkStr4(x_9, x_49, x_65, x_33);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_10);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_29);
lean_inc(x_11);
x_71 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_71, 0, x_11);
lean_ctor_set(x_71, 1, x_64);
lean_ctor_set(x_71, 2, x_67);
lean_ctor_set(x_71, 3, x_70);
x_72 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__10));
x_73 = l_Lean_Name_append(x_28, x_72);
x_74 = l_Lean_mkIdentFrom(x_26, x_73, x_20);
lean_dec(x_26);
lean_inc(x_22);
lean_inc(x_11);
x_75 = l_Lean_Syntax_node2(x_11, x_22, x_27, x_74);
lean_inc(x_11);
x_76 = l_Lean_Syntax_node2(x_11, x_21, x_71, x_75);
lean_inc(x_11);
x_77 = l_Lean_Syntax_node1(x_11, x_23, x_76);
lean_inc(x_11);
x_78 = l_Lean_Syntax_node2(x_11, x_32, x_77, x_46);
lean_inc(x_11);
x_79 = l_Lean_Syntax_node3(x_11, x_22, x_47, x_63, x_78);
lean_inc(x_11);
x_80 = l_Lean_Syntax_node1(x_11, x_17, x_79);
x_81 = l_Lean_Syntax_node2(x_11, x_30, x_16, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_15);
return x_82;
}
block_128:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_109 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__11));
x_110 = l_Lean_Name_mkStr4(x_9, x_94, x_86, x_109);
x_111 = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__3));
lean_inc(x_85);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_85);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13;
x_114 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__14));
lean_inc(x_107);
lean_inc(x_90);
x_115 = l_Lean_addMacroScope(x_90, x_114, x_107);
lean_inc(x_103);
lean_inc(x_85);
x_116 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_116, 0, x_85);
lean_ctor_set(x_116, 1, x_113);
lean_ctor_set(x_116, 2, x_115);
lean_ctor_set(x_116, 3, x_103);
x_117 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__15));
lean_inc(x_85);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_85);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17;
x_120 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__18));
lean_inc(x_107);
lean_inc(x_90);
x_121 = l_Lean_addMacroScope(x_90, x_120, x_107);
x_122 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20));
lean_inc(x_84);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_84);
lean_inc(x_103);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_103);
lean_inc(x_85);
x_125 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_125, 0, x_85);
lean_ctor_set(x_125, 1, x_119);
lean_ctor_set(x_125, 2, x_121);
lean_ctor_set(x_125, 3, x_124);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_126; 
x_126 = l_Lean_instQuoteNameMkStr1___private__1(x_89);
x_10 = x_84;
x_11 = x_85;
x_12 = x_90;
x_13 = x_118;
x_14 = x_108;
x_15 = x_96;
x_16 = x_99;
x_17 = x_101;
x_18 = x_125;
x_19 = x_87;
x_20 = x_88;
x_21 = x_92;
x_22 = x_91;
x_23 = x_93;
x_24 = x_116;
x_25 = x_112;
x_26 = x_95;
x_27 = x_98;
x_28 = x_97;
x_29 = x_103;
x_30 = x_102;
x_31 = x_110;
x_32 = x_105;
x_33 = x_104;
x_34 = x_106;
x_35 = x_107;
x_36 = x_126;
goto block_83;
}
else
{
lean_object* x_127; 
lean_dec(x_89);
x_127 = lean_ctor_get(x_100, 0);
lean_inc(x_127);
lean_dec_ref(x_100);
x_10 = x_84;
x_11 = x_85;
x_12 = x_90;
x_13 = x_118;
x_14 = x_108;
x_15 = x_96;
x_16 = x_99;
x_17 = x_101;
x_18 = x_125;
x_19 = x_87;
x_20 = x_88;
x_21 = x_92;
x_22 = x_91;
x_23 = x_93;
x_24 = x_116;
x_25 = x_112;
x_26 = x_95;
x_27 = x_98;
x_28 = x_97;
x_29 = x_103;
x_30 = x_102;
x_31 = x_110;
x_32 = x_105;
x_33 = x_104;
x_34 = x_106;
x_35 = x_107;
x_36 = x_127;
goto block_83;
}
}
block_168:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 5);
lean_inc(x_140);
lean_dec_ref(x_135);
x_141 = 0;
x_142 = l_Lean_SourceInfo_fromRef(x_140, x_141);
lean_dec(x_140);
x_143 = ((lean_object*)(l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1));
x_144 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21));
x_145 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22));
x_146 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23));
lean_inc(x_142);
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_145);
x_148 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25));
x_149 = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__5));
x_150 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27));
x_151 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29));
x_152 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31));
x_153 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33;
x_154 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34));
x_155 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35));
lean_inc(x_139);
lean_inc(x_138);
x_156 = l_Lean_addMacroScope(x_138, x_155, x_139);
x_157 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36));
lean_inc(x_129);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_129);
x_159 = lean_box(0);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
lean_inc(x_142);
x_161 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_161, 0, x_142);
lean_ctor_set(x_161, 1, x_153);
lean_ctor_set(x_161, 2, x_156);
lean_ctor_set(x_161, 3, x_160);
x_162 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38));
x_163 = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39));
lean_inc(x_142);
x_164 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_164, 0, x_142);
lean_ctor_set(x_164, 1, x_163);
lean_inc(x_131);
lean_inc_ref(x_164);
lean_inc(x_142);
x_165 = l_Lean_Syntax_node3(x_142, x_162, x_164, x_164, x_131);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_166; 
x_166 = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60;
x_84 = x_129;
x_85 = x_142;
x_86 = x_144;
x_87 = x_161;
x_88 = x_141;
x_89 = x_134;
x_90 = x_138;
x_91 = x_149;
x_92 = x_152;
x_93 = x_151;
x_94 = x_143;
x_95 = x_131;
x_96 = x_130;
x_97 = x_132;
x_98 = x_137;
x_99 = x_147;
x_100 = x_133;
x_101 = x_148;
x_102 = x_146;
x_103 = x_159;
x_104 = x_154;
x_105 = x_150;
x_106 = x_165;
x_107 = x_139;
x_108 = x_166;
goto block_128;
}
else
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_136, 0);
lean_inc(x_167);
lean_dec_ref(x_136);
x_84 = x_129;
x_85 = x_142;
x_86 = x_144;
x_87 = x_161;
x_88 = x_141;
x_89 = x_134;
x_90 = x_138;
x_91 = x_149;
x_92 = x_152;
x_93 = x_151;
x_94 = x_143;
x_95 = x_131;
x_96 = x_130;
x_97 = x_132;
x_98 = x_137;
x_99 = x_147;
x_100 = x_133;
x_101 = x_148;
x_102 = x_146;
x_103 = x_159;
x_104 = x_154;
x_105 = x_150;
x_106 = x_165;
x_107 = x_139;
x_108 = x_167;
goto block_128;
}
}
block_198:
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Lean_TSyntax_getId(x_169);
lean_inc_ref(x_172);
lean_inc(x_175);
x_176 = l_Lean_Macro_resolveGlobalName(x_175, x_172, x_171);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 1)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec_ref(x_177);
if (lean_obj_tag(x_180) == 0)
{
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec_ref(x_176);
x_182 = lean_ctor_get(x_178, 0);
lean_inc(x_182);
lean_dec(x_178);
lean_inc(x_175);
x_183 = l_Lean_instQuoteNameMkStr1___private__1(x_175);
x_129 = x_179;
x_130 = x_181;
x_131 = x_169;
x_132 = x_175;
x_133 = x_170;
x_134 = x_182;
x_135 = x_172;
x_136 = x_173;
x_137 = x_183;
goto block_168;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_176, 1);
lean_inc(x_184);
lean_dec_ref(x_176);
x_185 = lean_ctor_get(x_178, 0);
lean_inc(x_185);
lean_dec(x_178);
x_186 = lean_ctor_get(x_174, 0);
lean_inc(x_186);
lean_dec_ref(x_174);
x_187 = l_Lean_TSyntax_getString(x_186);
lean_dec(x_186);
x_188 = lean_box(0);
x_189 = l_Lean_Name_str___override(x_188, x_187);
x_190 = l_Lean_instQuoteNameMkStr1___private__1(x_189);
x_129 = x_179;
x_130 = x_184;
x_131 = x_169;
x_132 = x_175;
x_133 = x_170;
x_134 = x_185;
x_135 = x_172;
x_136 = x_173;
x_137 = x_190;
goto block_168;
}
}
else
{
lean_object* x_191; 
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_169);
x_191 = lean_ctor_get(x_176, 1);
lean_inc(x_191);
lean_dec_ref(x_176);
x_4 = x_172;
x_5 = x_191;
goto block_8;
}
}
else
{
lean_object* x_192; 
lean_dec(x_179);
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_169);
x_192 = lean_ctor_get(x_176, 1);
lean_inc(x_192);
lean_dec_ref(x_176);
x_4 = x_172;
x_5 = x_192;
goto block_8;
}
}
else
{
lean_object* x_193; 
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_169);
x_193 = lean_ctor_get(x_176, 1);
lean_inc(x_193);
lean_dec_ref(x_176);
x_4 = x_172;
x_5 = x_193;
goto block_8;
}
}
else
{
uint8_t x_194; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec(x_170);
lean_dec(x_169);
x_194 = !lean_is_exclusive(x_176);
if (x_194 == 0)
{
return x_176;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_176, 0);
x_196 = lean_ctor_get(x_176, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_176);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
block_210:
{
lean_object* x_205; 
x_205 = l_Lean_Syntax_getOptional_x3f(x_199);
lean_dec(x_199);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_box(0);
x_169 = x_200;
x_170 = x_201;
x_171 = x_202;
x_172 = x_203;
x_173 = x_204;
x_174 = x_206;
goto block_198;
}
else
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_205);
if (x_207 == 0)
{
x_169 = x_200;
x_170 = x_201;
x_171 = x_202;
x_172 = x_203;
x_173 = x_204;
x_174 = x_205;
goto block_198;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_205, 0);
lean_inc(x_208);
lean_dec(x_205);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_208);
x_169 = x_200;
x_170 = x_201;
x_171 = x_202;
x_172 = x_203;
x_173 = x_204;
x_174 = x_209;
goto block_198;
}
}
}
block_225:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_214 = lean_unsigned_to_nat(2u);
x_215 = l_Lean_Syntax_getArg(x_1, x_214);
x_216 = lean_unsigned_to_nat(3u);
x_217 = l_Lean_Syntax_getArg(x_1, x_216);
x_218 = lean_unsigned_to_nat(4u);
x_219 = l_Lean_Syntax_getArg(x_1, x_218);
lean_dec(x_1);
x_220 = l_Lean_Syntax_getOptional_x3f(x_219);
lean_dec(x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
x_221 = lean_box(0);
x_199 = x_215;
x_200 = x_217;
x_201 = x_211;
x_202 = x_213;
x_203 = x_212;
x_204 = x_221;
goto block_210;
}
else
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_220);
if (x_222 == 0)
{
x_199 = x_215;
x_200 = x_217;
x_201 = x_211;
x_202 = x_213;
x_203 = x_212;
x_204 = x_220;
goto block_210;
}
else
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_220, 0);
lean_inc(x_223);
lean_dec(x_220);
x_224 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_224, 0, x_223);
x_199 = x_215;
x_200 = x_217;
x_201 = x_211;
x_202 = x_213;
x_203 = x_212;
x_204 = x_224;
goto block_210;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_node(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppHardLineUnlessUngrouped_formatter___boxed), 5, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppAllowUngrouped_formatter___boxed), 5, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_skip;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppHardSpace_formatter___boxed), 5, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_138; lean_object* x_150; lean_object* x_151; lean_object* x_162; 
x_2 = ((lean_object*)(l_Lean_Parser_patternIgnore_formatter___closed__1));
x_97 = ((lean_object*)(l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0));
x_98 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__34_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_99 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__35_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_150 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__53_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_162 = l_Lean_Parser_registerAlias(x_2, x_97, x_98, x_99, x_150);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec_ref(x_162);
x_163 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__62_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_164 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_2, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
lean_dec_ref(x_164);
x_165 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__64_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_166 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_2, x_165);
x_151 = x_166;
goto block_161;
}
else
{
x_151 = x_164;
goto block_161;
}
}
else
{
x_151 = x_162;
goto block_161;
}
block_14:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_5);
x_6 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__7_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_7 = ((lean_object*)(l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1));
x_8 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__8_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_9 = l_Lean_Parser_registerAlias(x_6, x_7, x_4, x_8, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_9);
x_10 = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
x_11 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_11);
x_12 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_13 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_6, x_12);
return x_13;
}
else
{
return x_11;
}
}
else
{
return x_9;
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
block_26:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_17);
x_18 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__11_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_19 = ((lean_object*)(l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1));
x_20 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__12_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(x_15);
lean_inc_ref(x_16);
x_21 = l_Lean_Parser_registerAlias(x_18, x_19, x_16, x_20, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_21);
x_22 = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
x_23 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_18, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_23);
x_24 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_25 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_18, x_24);
x_3 = x_15;
x_4 = x_16;
x_5 = x_25;
goto block_14;
}
else
{
x_3 = x_15;
x_4 = x_16;
x_5 = x_23;
goto block_14;
}
}
else
{
x_3 = x_15;
x_4 = x_16;
x_5 = x_21;
goto block_14;
}
}
else
{
lean_dec_ref(x_16);
lean_dec_ref(x_15);
return x_17;
}
}
block_40:
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_30);
x_31 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__14_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_32 = ((lean_object*)(l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1));
x_33 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_34 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__16_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_35 = l_Lean_Parser_registerAlias(x_31, x_32, x_33, x_34, x_29);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_35);
x_36 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__18_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_37 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_31, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_37);
x_38 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_39 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_31, x_38);
x_15 = x_27;
x_16 = x_28;
x_17 = x_39;
goto block_26;
}
else
{
x_15 = x_27;
x_16 = x_28;
x_17 = x_37;
goto block_26;
}
}
else
{
x_15 = x_27;
x_16 = x_28;
x_17 = x_35;
goto block_26;
}
}
else
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
return x_30;
}
}
block_54:
{
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_44);
x_45 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__20_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_46 = ((lean_object*)(l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1));
x_47 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_48 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__21_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(x_43);
x_49 = l_Lean_Parser_registerAlias(x_45, x_46, x_47, x_48, x_43);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_49);
x_50 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__23_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_51 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_45, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_51);
x_52 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_53 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_45, x_52);
x_27 = x_41;
x_28 = x_42;
x_29 = x_43;
x_30 = x_53;
goto block_40;
}
else
{
x_27 = x_41;
x_28 = x_42;
x_29 = x_43;
x_30 = x_51;
goto block_40;
}
}
else
{
x_27 = x_41;
x_28 = x_42;
x_29 = x_43;
x_30 = x_49;
goto block_40;
}
}
else
{
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
return x_44;
}
}
block_68:
{
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_58);
x_59 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__24_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_60 = ((lean_object*)(l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1));
x_61 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_62 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__25_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(x_57);
x_63 = l_Lean_Parser_registerAlias(x_59, x_60, x_61, x_62, x_57);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_63);
x_64 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__27_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_65 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_59, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_65);
x_66 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_67 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_59, x_66);
x_41 = x_55;
x_42 = x_56;
x_43 = x_57;
x_44 = x_67;
goto block_54;
}
else
{
x_41 = x_55;
x_42 = x_56;
x_43 = x_57;
x_44 = x_65;
goto block_54;
}
}
else
{
x_41 = x_55;
x_42 = x_56;
x_43 = x_57;
x_44 = x_63;
goto block_54;
}
}
else
{
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec_ref(x_55);
return x_58;
}
}
block_82:
{
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_72);
x_73 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__28_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_74 = ((lean_object*)(l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1));
x_75 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_76 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__29_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(x_71);
x_77 = l_Lean_Parser_registerAlias(x_73, x_74, x_75, x_76, x_71);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_77);
x_78 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__30_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_79 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_73, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_79);
x_80 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_81 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_73, x_80);
x_55 = x_69;
x_56 = x_70;
x_57 = x_71;
x_58 = x_81;
goto block_68;
}
else
{
x_55 = x_69;
x_56 = x_70;
x_57 = x_71;
x_58 = x_79;
goto block_68;
}
}
else
{
x_55 = x_69;
x_56 = x_70;
x_57 = x_71;
x_58 = x_77;
goto block_68;
}
}
else
{
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec_ref(x_69);
return x_72;
}
}
block_96:
{
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_86);
x_87 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__31_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_88 = ((lean_object*)(l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1));
x_89 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_90 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__32_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(x_85);
x_91 = l_Lean_Parser_registerAlias(x_87, x_88, x_89, x_90, x_85);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_91);
x_92 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__33_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_93 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_87, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_93);
x_94 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_95 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_87, x_94);
x_69 = x_83;
x_70 = x_84;
x_71 = x_85;
x_72 = x_95;
goto block_82;
}
else
{
x_69 = x_83;
x_70 = x_84;
x_71 = x_85;
x_72 = x_93;
goto block_82;
}
}
else
{
x_69 = x_83;
x_70 = x_84;
x_71 = x_85;
x_72 = x_91;
goto block_82;
}
}
else
{
lean_dec_ref(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_83);
return x_86;
}
}
block_113:
{
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec_ref(x_102);
x_103 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__36_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_104 = ((lean_object*)(l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1));
x_105 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_106 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__37_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_107 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__38_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_108 = l_Lean_Parser_registerAlias(x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_108);
x_109 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__40_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_110 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_103, x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_110);
x_111 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_112 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_103, x_111);
x_83 = x_100;
x_84 = x_101;
x_85 = x_107;
x_86 = x_112;
goto block_96;
}
else
{
x_83 = x_100;
x_84 = x_101;
x_85 = x_107;
x_86 = x_110;
goto block_96;
}
}
else
{
x_83 = x_100;
x_84 = x_101;
x_85 = x_107;
x_86 = x_108;
goto block_96;
}
}
else
{
lean_dec_ref(x_101);
lean_dec_ref(x_100);
return x_102;
}
}
block_125:
{
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_116);
x_117 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__41_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_118 = ((lean_object*)(l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1));
x_119 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__42_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(x_114);
lean_inc_ref(x_115);
x_120 = l_Lean_Parser_registerAlias(x_117, x_118, x_115, x_119, x_114);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec_ref(x_120);
x_121 = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
x_122 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_117, x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_122);
x_123 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_124 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_117, x_123);
x_100 = x_114;
x_101 = x_115;
x_102 = x_124;
goto block_113;
}
else
{
x_100 = x_114;
x_101 = x_115;
x_102 = x_122;
goto block_113;
}
}
else
{
x_100 = x_114;
x_101 = x_115;
x_102 = x_120;
goto block_113;
}
}
else
{
lean_dec_ref(x_115);
lean_dec_ref(x_114);
return x_116;
}
}
block_137:
{
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec_ref(x_128);
x_129 = ((lean_object*)(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22));
x_130 = ((lean_object*)(l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1));
x_131 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__44_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(x_126);
lean_inc_ref(x_127);
x_132 = l_Lean_Parser_registerAlias(x_129, x_130, x_127, x_131, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec_ref(x_132);
x_133 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__45_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_134 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_129, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec_ref(x_134);
x_135 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_136 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_129, x_135);
x_114 = x_126;
x_115 = x_127;
x_116 = x_136;
goto block_125;
}
else
{
x_114 = x_126;
x_115 = x_127;
x_116 = x_134;
goto block_125;
}
}
else
{
x_114 = x_126;
x_115 = x_127;
x_116 = x_132;
goto block_125;
}
}
else
{
lean_dec_ref(x_127);
lean_dec_ref(x_126);
return x_128;
}
}
block_149:
{
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec_ref(x_138);
x_139 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__46_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_140 = ((lean_object*)(l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1));
x_141 = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
x_142 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__48_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_143 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__50_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_144 = l_Lean_Parser_registerAlias(x_139, x_140, x_141, x_142, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_144);
x_145 = l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
x_146 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_139, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec_ref(x_146);
x_147 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_148 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_139, x_147);
x_126 = x_143;
x_127 = x_141;
x_128 = x_148;
goto block_137;
}
else
{
x_126 = x_143;
x_127 = x_141;
x_128 = x_146;
goto block_137;
}
}
else
{
x_126 = x_143;
x_127 = x_141;
x_128 = x_144;
goto block_137;
}
}
else
{
return x_138;
}
}
block_161:
{
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec_ref(x_151);
x_152 = ((lean_object*)(l_Lean_Parser_group_formatter___closed__1));
x_153 = ((lean_object*)(l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0));
x_154 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__55_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_155 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__56_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_156 = l_Lean_Parser_registerAlias(x_152, x_153, x_154, x_155, x_150);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec_ref(x_156);
x_157 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__58_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_158 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_152, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; 
lean_dec_ref(x_158);
x_159 = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__60_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
x_160 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_152, x_159);
x_138 = x_160;
goto block_149;
}
else
{
x_138 = x_158;
goto block_149;
}
}
else
{
x_138 = x_156;
goto block_149;
}
}
else
{
return x_151;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin);
lean_object* initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* initialize_Lean_Hygiene(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Extra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Hygiene(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_antiquotExpr_formatter___closed__2 = _init_l_Lean_Parser_antiquotExpr_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_antiquotExpr_formatter___closed__2);
if (builtin) {res = l_Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_antiquotExpr_parenthesizer___closed__1 = _init_l_Lean_Parser_antiquotExpr_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_antiquotExpr_parenthesizer___closed__1);
l_Lean_Parser_mkAntiquot_parenthesizer___closed__3 = _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_parenthesizer___closed__3);
l_Lean_Parser_mkAntiquot_parenthesizer___closed__4 = _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_mkAntiquot_parenthesizer___closed__4);
l_Lean_Parser_optional___closed__0 = _init_l_Lean_Parser_optional___closed__0();
lean_mark_persistent(l_Lean_Parser_optional___closed__0);
if (builtin) {res = l_Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_many___closed__0 = _init_l_Lean_Parser_many___closed__0();
lean_mark_persistent(l_Lean_Parser_many___closed__0);
if (builtin) {res = l_Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_ident_formatter___closed__2 = _init_l_Lean_Parser_ident_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_ident_formatter___closed__2);
l_Lean_Parser_ident_parenthesizer___closed__0 = _init_l_Lean_Parser_ident_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_ident_parenthesizer___closed__0);
l_Lean_Parser_ident___closed__0 = _init_l_Lean_Parser_ident___closed__0();
lean_mark_persistent(l_Lean_Parser_ident___closed__0);
l_Lean_Parser_ident___closed__1 = _init_l_Lean_Parser_ident___closed__1();
lean_mark_persistent(l_Lean_Parser_ident___closed__1);
l_Lean_Parser_ident = _init_l_Lean_Parser_ident();
lean_mark_persistent(l_Lean_Parser_ident);
if (builtin) {res = l_Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2 = _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2);
l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3 = _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3);
l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4 = _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4);
l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5 = _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5);
l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1 = _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1);
l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2 = _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2);
l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3 = _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3);
l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4 = _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4);
l_Lean_Parser_identWithPartialTrailingDot___closed__1 = _init_l_Lean_Parser_identWithPartialTrailingDot___closed__1();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot___closed__1);
l_Lean_Parser_identWithPartialTrailingDot___closed__2 = _init_l_Lean_Parser_identWithPartialTrailingDot___closed__2();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot___closed__2);
l_Lean_Parser_identWithPartialTrailingDot___closed__3 = _init_l_Lean_Parser_identWithPartialTrailingDot___closed__3();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot___closed__3);
l_Lean_Parser_identWithPartialTrailingDot___closed__4 = _init_l_Lean_Parser_identWithPartialTrailingDot___closed__4();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot___closed__4);
l_Lean_Parser_identWithPartialTrailingDot___closed__5 = _init_l_Lean_Parser_identWithPartialTrailingDot___closed__5();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot___closed__5);
l_Lean_Parser_identWithPartialTrailingDot___closed__6 = _init_l_Lean_Parser_identWithPartialTrailingDot___closed__6();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot___closed__6);
l_Lean_Parser_identWithPartialTrailingDot___closed__7 = _init_l_Lean_Parser_identWithPartialTrailingDot___closed__7();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot___closed__7);
l_Lean_Parser_identWithPartialTrailingDot = _init_l_Lean_Parser_identWithPartialTrailingDot();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot);
l_Lean_Parser_rawIdent___closed__0 = _init_l_Lean_Parser_rawIdent___closed__0();
lean_mark_persistent(l_Lean_Parser_rawIdent___closed__0);
l_Lean_Parser_rawIdent = _init_l_Lean_Parser_rawIdent();
lean_mark_persistent(l_Lean_Parser_rawIdent);
l_Lean_Parser_hygieneInfo_formatter___closed__2 = _init_l_Lean_Parser_hygieneInfo_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_hygieneInfo_formatter___closed__2);
l_Lean_Parser_hygieneInfo_parenthesizer___closed__0 = _init_l_Lean_Parser_hygieneInfo_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_hygieneInfo_parenthesizer___closed__0);
l_Lean_Parser_hygieneInfo___closed__0 = _init_l_Lean_Parser_hygieneInfo___closed__0();
lean_mark_persistent(l_Lean_Parser_hygieneInfo___closed__0);
l_Lean_Parser_hygieneInfo___closed__1 = _init_l_Lean_Parser_hygieneInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_hygieneInfo___closed__1);
l_Lean_Parser_hygieneInfo = _init_l_Lean_Parser_hygieneInfo();
lean_mark_persistent(l_Lean_Parser_hygieneInfo);
if (builtin) {res = l_Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_numLit_formatter___closed__2 = _init_l_Lean_Parser_numLit_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_numLit_formatter___closed__2);
l_Lean_Parser_numLit_parenthesizer___closed__0 = _init_l_Lean_Parser_numLit_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_numLit_parenthesizer___closed__0);
l_Lean_Parser_numLit___closed__0 = _init_l_Lean_Parser_numLit___closed__0();
lean_mark_persistent(l_Lean_Parser_numLit___closed__0);
l_Lean_Parser_numLit___closed__1 = _init_l_Lean_Parser_numLit___closed__1();
lean_mark_persistent(l_Lean_Parser_numLit___closed__1);
l_Lean_Parser_numLit = _init_l_Lean_Parser_numLit();
lean_mark_persistent(l_Lean_Parser_numLit);
if (builtin) {res = l_Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_hexnum___closed__2 = _init_l_Lean_Parser_hexnum___closed__2();
lean_mark_persistent(l_Lean_Parser_hexnum___closed__2);
l_Lean_Parser_hexnum___closed__3 = _init_l_Lean_Parser_hexnum___closed__3();
lean_mark_persistent(l_Lean_Parser_hexnum___closed__3);
l_Lean_Parser_hexnum = _init_l_Lean_Parser_hexnum();
lean_mark_persistent(l_Lean_Parser_hexnum);
if (builtin) {res = l_Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_scientificLit_formatter___closed__2 = _init_l_Lean_Parser_scientificLit_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_scientificLit_formatter___closed__2);
l_Lean_Parser_scientificLit_parenthesizer___closed__0 = _init_l_Lean_Parser_scientificLit_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_scientificLit_parenthesizer___closed__0);
l_Lean_Parser_scientificLit___closed__0 = _init_l_Lean_Parser_scientificLit___closed__0();
lean_mark_persistent(l_Lean_Parser_scientificLit___closed__0);
l_Lean_Parser_scientificLit___closed__1 = _init_l_Lean_Parser_scientificLit___closed__1();
lean_mark_persistent(l_Lean_Parser_scientificLit___closed__1);
l_Lean_Parser_scientificLit = _init_l_Lean_Parser_scientificLit();
lean_mark_persistent(l_Lean_Parser_scientificLit);
if (builtin) {res = l_Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_strLit_formatter___closed__2 = _init_l_Lean_Parser_strLit_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_strLit_formatter___closed__2);
l_Lean_Parser_strLit_parenthesizer___closed__0 = _init_l_Lean_Parser_strLit_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_strLit_parenthesizer___closed__0);
l_Lean_Parser_strLit___closed__0 = _init_l_Lean_Parser_strLit___closed__0();
lean_mark_persistent(l_Lean_Parser_strLit___closed__0);
l_Lean_Parser_strLit___closed__1 = _init_l_Lean_Parser_strLit___closed__1();
lean_mark_persistent(l_Lean_Parser_strLit___closed__1);
l_Lean_Parser_strLit = _init_l_Lean_Parser_strLit();
lean_mark_persistent(l_Lean_Parser_strLit);
if (builtin) {res = l_Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_charLit_formatter___closed__2 = _init_l_Lean_Parser_charLit_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_charLit_formatter___closed__2);
l_Lean_Parser_charLit_parenthesizer___closed__0 = _init_l_Lean_Parser_charLit_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_charLit_parenthesizer___closed__0);
l_Lean_Parser_charLit___closed__0 = _init_l_Lean_Parser_charLit___closed__0();
lean_mark_persistent(l_Lean_Parser_charLit___closed__0);
l_Lean_Parser_charLit___closed__1 = _init_l_Lean_Parser_charLit___closed__1();
lean_mark_persistent(l_Lean_Parser_charLit___closed__1);
l_Lean_Parser_charLit = _init_l_Lean_Parser_charLit();
lean_mark_persistent(l_Lean_Parser_charLit);
if (builtin) {res = l_Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_nameLit_formatter___closed__2 = _init_l_Lean_Parser_nameLit_formatter___closed__2();
lean_mark_persistent(l_Lean_Parser_nameLit_formatter___closed__2);
l_Lean_Parser_nameLit_parenthesizer___closed__0 = _init_l_Lean_Parser_nameLit_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_nameLit_parenthesizer___closed__0);
l_Lean_Parser_nameLit___closed__0 = _init_l_Lean_Parser_nameLit___closed__0();
lean_mark_persistent(l_Lean_Parser_nameLit___closed__0);
l_Lean_Parser_nameLit___closed__1 = _init_l_Lean_Parser_nameLit___closed__1();
lean_mark_persistent(l_Lean_Parser_nameLit___closed__1);
l_Lean_Parser_nameLit = _init_l_Lean_Parser_nameLit();
lean_mark_persistent(l_Lean_Parser_nameLit);
if (builtin) {res = l_Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_many1Indent___closed__1 = _init_l_Lean_Parser_many1Indent___closed__1();
lean_mark_persistent(l_Lean_Parser_many1Indent___closed__1);
if (builtin) {res = l_Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_sepByIndent___closed__0 = _init_l_Lean_Parser_sepByIndent___closed__0();
lean_mark_persistent(l_Lean_Parser_sepByIndent___closed__0);
l_Lean_Parser_sepByIndent___closed__2 = _init_l_Lean_Parser_sepByIndent___closed__2();
lean_mark_persistent(l_Lean_Parser_sepByIndent___closed__2);
l_Lean_Parser_sepByIndent___closed__3 = _init_l_Lean_Parser_sepByIndent___closed__3();
lean_mark_persistent(l_Lean_Parser_sepByIndent___closed__3);
l_Lean_Parser_sepByIndent___closed__4 = _init_l_Lean_Parser_sepByIndent___closed__4();
lean_mark_persistent(l_Lean_Parser_sepByIndent___closed__4);
l_Lean_Parser_sepByIndent_parenthesizer___closed__0 = _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Parser_sepByIndent_parenthesizer___closed__0);
l_Lean_Parser_sepByIndent_parenthesizer___closed__1 = _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Parser_sepByIndent_parenthesizer___closed__1);
if (builtin) {res = l_Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_ppHardSpace = _init_l_Lean_Parser_ppHardSpace();
lean_mark_persistent(l_Lean_Parser_ppHardSpace);
if (builtin) {res = l_Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_ppSpace = _init_l_Lean_Parser_ppSpace();
lean_mark_persistent(l_Lean_Parser_ppSpace);
if (builtin) {res = l_Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_ppLine = _init_l_Lean_Parser_ppLine();
lean_mark_persistent(l_Lean_Parser_ppLine);
if (builtin) {res = l_Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_ppAllowUngrouped = _init_l_Lean_Parser_ppAllowUngrouped();
lean_mark_persistent(l_Lean_Parser_ppAllowUngrouped);
if (builtin) {res = l_Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_ppHardLineUnlessUngrouped = _init_l_Lean_Parser_ppHardLineUnlessUngrouped();
lean_mark_persistent(l_Lean_Parser_ppHardLineUnlessUngrouped);
if (builtin) {res = l_Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_ppDedent_formatter___closed__0 = _init_l_Lean_ppDedent_formatter___closed__0();
lean_mark_persistent(l_Lean_ppDedent_formatter___closed__0);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59);
l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60 = _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60();
lean_mark_persistent(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60);
l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
