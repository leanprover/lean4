// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.DeclWithSig
// Imports: public import Lean.Parser.Types import Lean.Parser.Command
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
lean_object* l_Lean_Parser_Command_declSig_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Command_declSig_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_termParser(lean_object*);
extern lean_object* l_Lean_Parser_Command_declSig;
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__0_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__1_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Delaborator"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__2_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declSigWithId"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value),LEAN_SCALAR_PTR_LITERAL(125, 120, 113, 218, 19, 40, 2, 236)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__5 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__5_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__6;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Command_declSig_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__7 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__7_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__8;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__9;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value),LEAN_SCALAR_PTR_LITERAL(125, 120, 113, 218, 19, 40, 2, 236)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value_aux_3),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 11, 240, 161, 120, 65, 104, 126)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___boxed(lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__0_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__1;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Command_declSig_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__2_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parenthesizer"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3_value),LEAN_SCALAR_PTR_LITERAL(125, 120, 113, 218, 19, 40, 2, 236)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value_aux_3),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 108, 232, 98, 107, 255, 86, 176)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___boxed(lean_object*);
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__0;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__1;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__2;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__3;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__4;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId;
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__6(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = l_Lean_Parser_maxPrec;
v___x_18_ = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__8(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_20_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__7));
v___x_21_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__6, &l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__6_once, _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__6);
v___x_22_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_22_, 0, v___x_21_);
lean_closure_set(v___x_22_, 1, v___x_20_);
return v___x_22_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__9(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_23_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__8, &l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__8_once, _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__8);
v___x_24_ = lean_unsigned_to_nat(1024u);
v___x_25_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4));
v___x_26_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_26_, 0, v___x_25_);
lean_closure_set(v___x_26_, 1, v___x_24_);
lean_closure_set(v___x_26_, 2, v___x_23_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter(lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__5));
v___x_33_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__9, &l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__9_once, _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__9);
v___x_34_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_32_, v___x_33_, v_a_27_, v_a_28_, v_a_29_, v_a_30_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___boxed(lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter(v_a_35_, v_a_36_, v_a_37_, v_a_38_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3(){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_49_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_50_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4));
v___x_51_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___closed__1));
v___x_52_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___boxed), 5, 0);
v___x_53_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_49_, v___x_50_, v___x_51_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3___boxed(lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3();
return v_res_55_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = l_Lean_Parser_maxPrec;
v___x_64_ = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__2));
v___x_67_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__1, &l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__1);
v___x_68_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_68_, 0, v___x_67_);
lean_closure_set(v___x_68_, 1, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__3, &l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__3_once, _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__3);
v___x_70_ = lean_unsigned_to_nat(1024u);
v___x_71_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4));
v___x_72_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_72_, 0, v___x_71_);
lean_closure_set(v___x_72_, 1, v___x_70_);
lean_closure_set(v___x_72_, 2, v___x_69_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer(lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__0));
v___x_79_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__4, &l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__4_once, _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___closed__4);
v___x_80_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_78_, v___x_79_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___boxed(lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer(v_a_81_, v_a_82_, v_a_83_, v_a_84_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7(){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_95_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_96_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4));
v___x_97_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___closed__1));
v___x_98_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer___boxed), 5, 0);
v___x_99_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_95_, v___x_96_, v___x_97_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7___boxed(lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7();
return v_res_101_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__0(void){
_start:
{
uint8_t v___x_102_; uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_102_ = 0;
v___x_103_ = 1;
v___x_104_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4));
v___x_105_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__3));
v___x_106_ = l_Lean_Parser_mkAntiquot(v___x_105_, v___x_104_, v___x_103_, v___x_102_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__1(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = l_Lean_Parser_maxPrec;
v___x_108_ = l_Lean_Parser_termParser(v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__2(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = l_Lean_Parser_Command_declSig;
v___x_110_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__1, &l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__1);
v___x_111_ = l_Lean_Parser_andthen(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__3(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__2, &l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__2_once, _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__2);
v___x_113_ = lean_unsigned_to_nat(1024u);
v___x_114_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4));
v___x_115_ = l_Lean_Parser_leadingNode(v___x_114_, v___x_113_, v___x_112_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__4(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__3, &l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__3_once, _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__3);
v___x_117_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__0, &l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__0);
v___x_118_ = l_Lean_Parser_withAntiquot(v___x_117_, v___x_116_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__5(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__4, &l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__4_once, _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__4);
v___x_120_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter___closed__4));
v___x_121_ = l_Lean_Parser_withCache(v___x_120_, v___x_119_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__5, &l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__5_once, _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId___closed__5);
return v___x_122_;
}
}
lean_object* runtime_initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_DeclWithSig(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_DeclWithSig_0__Lean_PrettyPrinter_Delaborator_declSigWithId___regBuiltin_Lean_PrettyPrinter_Delaborator_declSigWithId_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_Delaborator_declSigWithId = _init_l_Lean_PrettyPrinter_Delaborator_declSigWithId();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_declSigWithId);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_PrettyPrinter_Delaborator_DeclWithSig(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Delaborator_DeclWithSig(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Delaborator_DeclWithSig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_PrettyPrinter_Delaborator_DeclWithSig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_PrettyPrinter_Delaborator_DeclWithSig(builtin);
}
#ifdef __cplusplus
}
#endif
