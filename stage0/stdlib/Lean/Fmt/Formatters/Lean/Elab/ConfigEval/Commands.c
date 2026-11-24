// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Elab.ConfigEval.Commands
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Lean.Parser.Term meta import Lean.Elab.ConfigEval.Commands meta import Lean.Parser.Command import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_convertBracketedBinders(lean_object*);
lean_object* l_Lean_Fmt_fmtBinders(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtSeq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalInstance___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalInstance___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ConfigEval"};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ensureEvalTermInstance"};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__8_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__8_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__8_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__7_value),LEAN_SCALAR_PTR_LITERAL(188, 241, 114, 217, 47, 253, 4, 219)}};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalTermInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalTermInstance___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "fmtEnsureEvalTermInstance"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(12, 29, 196, 188, 222, 217, 61, 155)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ensureEvalExprInstance"};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 108, 175, 10, 248, 93, 94, 3)}};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalExprInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalExprInstance___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "fmtEnsureEvalExprInstance"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 44, 94, 143, 249, 106, 103, 46)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "ensureEvalTermExprInstances"};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 66, 158, 168, 204, 221, 79, 184)}};
static const lean_object* l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalTermExprInstances(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalTermExprInstances___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "fmtEnsureEvalTermExprInstances"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 233, 165, 192, 67, 162, 184, 50)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "deriveEvalExprUsingMeta"};
static const lean_object* l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 116, 75, 98, 130, 21, 177, 80)}};
static const lean_object* l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeriveEvalExprUsingMeta(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "fmtDeriveEvalExprUsingMeta"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 247, 105, 13, 202, 28, 190, 45)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConfigEntryOmit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "configEntryOmit"};
static const lean_object* l_Lean_Fmt_fmtConfigEntryOmit___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntryOmit___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryOmit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryOmit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryOmit___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryOmit___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryOmit___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryOmit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryOmit___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConfigEntryOmit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 140, 111, 202, 251, 168, 170, 75)}};
static const lean_object* l_Lean_Fmt_fmtConfigEntryOmit___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntryOmit___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConfigEntryOmit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtConfigEntryOmit___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntryOmit___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryOmit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryOmit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtConfigEntryOmit"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 13, 116, 12, 225, 97, 199, 154)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "configEntryHandlerKeyPrefix"};
static const lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 45, 37, 228, 14, 221, 193, 71)}};
static const lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "fmtConfigEntryHandlerKeyPrefix"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 233, 58, 201, 207, 171, 152, 120)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "configEntryHandlerKey"};
static const lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 190, 73, 235, 170, 184, 39, 210)}};
static const lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "configEntryHandlerKeyWildcard"};
static const lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 192, 13, 21, 20, 44, 232, 93)}};
static const lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKey(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKey___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtConfigEntryHandlerKey"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 190, 77, 168, 124, 199, 217, 134)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConfigEntryHandler___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "configEntryHandler"};
static const lean_object* l_Lean_Fmt_fmtConfigEntryHandler___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntryHandler___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandler___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandler___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandler___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandler___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandler___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntryHandler___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandler___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConfigEntryHandler___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 145, 34, 65, 77, 53, 67, 42)}};
static const lean_object* l_Lean_Fmt_fmtConfigEntryHandler___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntryHandler___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryHandler___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtConfigEntryHandler"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 172, 224, 172, 2, 147, 1, 235)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConfigEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "configEntry"};
static const lean_object* l_Lean_Fmt_fmtConfigEntry___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntry___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntry___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntry___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntry___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntry___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigEntry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigEntry___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConfigEntry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 149, 160, 204, 146, 200, 218, 133)}};
static const lean_object* l_Lean_Fmt_fmtConfigEntry___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConfigEntry___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntry___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtConfigEntry"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 53, 202, 11, 197, 144, 80, 2)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtWithConfigEntries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "configEntries"};
static const lean_object* l_Lean_Fmt_fmtWithConfigEntries___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtWithConfigEntries___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtWithConfigEntries___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtWithConfigEntries___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWithConfigEntries___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtWithConfigEntries___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWithConfigEntries___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtWithConfigEntries___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWithConfigEntries___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtWithConfigEntries___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 127, 108, 166, 156, 181, 170, 30)}};
static const lean_object* l_Lean_Fmt_fmtWithConfigEntries___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtWithConfigEntries___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtWithConfigEntries___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Fmt_fmtWithConfigEntries___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtWithConfigEntries___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithConfigEntries(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithConfigEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDefEvalConfigItemCmd_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDefEvalConfigItemCmd_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "defEvalConfigItemCmd"};
static const lean_object* l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 50, 201, 157, 117, 233, 235, 218)}};
static const lean_object* l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDefEvalConfigItemCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDefEvalConfigItemCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "fmtDefEvalConfigItemCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 58, 92, 117, 110, 52, 177, 183)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "declareCoreConfigElab"};
static const lean_object* l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 30, 123, 201, 158, 66, 128, 147)}};
static const lean_object* l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareCoreConfigElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareCoreConfigElab___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtDeclareCoreConfigElab"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 36, 34, 3, 79, 242, 68, 212)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDeclareTermConfigElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "declareTermConfigElab"};
static const lean_object* l_Lean_Fmt_fmtDeclareTermConfigElab___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDeclareTermConfigElab___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeclareTermConfigElab___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareTermConfigElab___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareTermConfigElab___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareTermConfigElab___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareTermConfigElab___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareTermConfigElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareTermConfigElab___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDeclareTermConfigElab___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 108, 165, 103, 249, 154, 177, 123)}};
static const lean_object* l_Lean_Fmt_fmtDeclareTermConfigElab___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDeclareTermConfigElab___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareTermConfigElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareTermConfigElab___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtDeclareTermConfigElab"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 210, 76, 76, 19, 255, 222, 73)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDeclareTacticConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "declareTacticConfig"};
static const lean_object* l_Lean_Fmt_fmtDeclareTacticConfig___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDeclareTacticConfig___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeclareTacticConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareTacticConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareTacticConfig___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareTacticConfig___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareTacticConfig___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareTacticConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareTacticConfig___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDeclareTacticConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 17, 172, 247, 161, 0, 3, 195)}};
static const lean_object* l_Lean_Fmt_fmtDeclareTacticConfig___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDeclareTacticConfig___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareTacticConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareTacticConfig___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtDeclareTacticConfig"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 79, 202, 94, 102, 123, 176, 102)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDeclareCommandConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "declareCommandConfig"};
static const lean_object* l_Lean_Fmt_fmtDeclareCommandConfig___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDeclareCommandConfig___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeclareCommandConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareCommandConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareCommandConfig___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareCommandConfig___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareCommandConfig___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareCommandConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareCommandConfig___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDeclareCommandConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 49, 172, 65, 140, 146, 127, 103)}};
static const lean_object* l_Lean_Fmt_fmtDeclareCommandConfig___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDeclareCommandConfig___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareCommandConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareCommandConfig___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "fmtDeclareCommandConfig"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 18, 209, 52, 77, 137, 116, 74)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalInstance(lean_object* v_visibility_x3f_4_, lean_object* v_attrKind_5_, lean_object* v_keywordTk_6_, lean_object* v_type_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Fmt_fmt(v_keywordTk_6_, v_a_8_, v_a_9_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v_a_12_; lean_object* v___x_13_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_a_11_);
v_a_12_ = lean_ctor_get(v___x_10_, 1);
lean_inc(v_a_12_);
lean_dec_ref_known(v___x_10_, 2);
v___x_13_ = l_Lean_Fmt_fmt(v_type_7_, v_a_8_, v_a_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v_a_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
v_a_15_ = lean_ctor_get(v___x_13_, 1);
lean_inc(v_a_15_);
lean_dec_ref_known(v___x_13_, 2);
v___x_16_ = lean_unsigned_to_nat(2u);
v___x_17_ = lean_mk_empty_array_with_capacity(v___x_16_);
lean_inc_ref(v___x_17_);
v___x_18_ = lean_array_push(v___x_17_, v_a_11_);
v___x_19_ = lean_array_push(v___x_18_, v_a_14_);
v___x_20_ = ((lean_object*)(l_Lean_Fmt_fmtEnsureEvalInstance___closed__0));
v___x_21_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_19_, v___x_20_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_23_, 0, v_attrKind_5_);
v___x_24_ = lean_array_push(v___x_17_, v_visibility_x3f_4_);
v___x_25_ = lean_array_push(v___x_24_, v___x_23_);
v___x_26_ = l_Lean_Fmt_fmtDeclWithModifiers(v___x_22_, v___x_22_, v___x_25_, v___x_21_, v_a_8_, v_a_15_);
lean_dec_ref(v___x_25_);
return v___x_26_;
}
else
{
lean_dec(v_a_11_);
lean_dec(v_attrKind_5_);
lean_dec(v_visibility_x3f_4_);
return v___x_13_;
}
}
else
{
lean_dec(v_type_7_);
lean_dec(v_attrKind_5_);
lean_dec(v_visibility_x3f_4_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalInstance___boxed(lean_object* v_visibility_x3f_27_, lean_object* v_attrKind_28_, lean_object* v_keywordTk_29_, lean_object* v_type_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Fmt_fmtEnsureEvalInstance(v_visibility_x3f_27_, v_attrKind_28_, v_keywordTk_29_, v_type_30_, v_a_31_, v_a_32_);
lean_dec_ref(v_a_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalTermInstance(lean_object* v_x_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_visibility_x3f_55_; lean_object* v___y_56_; lean_object* v___y_57_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = ((lean_object*)(l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__8));
lean_inc(v_x_51_);
v___x_80_ = l_Lean_Syntax_isOfKind(v_x_51_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_x_51_);
v___x_81_ = l_Lean_Fmt_Error_partialFormatter;
v___x_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v_a_53_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = l_Lean_Syntax_getArg(v_x_51_, v___x_83_);
v___x_85_ = l_Lean_Syntax_isNone(v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_84_);
v___x_87_ = l_Lean_Syntax_matchesNull(v___x_84_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v___x_84_);
lean_dec(v_x_51_);
v___x_88_ = l_Lean_Fmt_Error_partialFormatter;
v___x_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v_a_53_);
return v___x_89_;
}
else
{
lean_object* v_visibility_x3f_90_; lean_object* v___x_91_; 
v_visibility_x3f_90_ = l_Lean_Syntax_getArg(v___x_84_, v___x_83_);
lean_dec(v___x_84_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_visibility_x3f_90_);
v_visibility_x3f_55_ = v___x_91_;
v___y_56_ = v_a_52_;
v___y_57_ = v_a_53_;
goto v___jp_54_;
}
}
else
{
lean_object* v___x_92_; 
lean_dec(v___x_84_);
v___x_92_ = lean_box(0);
v_visibility_x3f_55_ = v___x_92_;
v___y_56_ = v_a_52_;
v___y_57_ = v_a_53_;
goto v___jp_54_;
}
}
v___jp_54_:
{
lean_object* v___x_58_; lean_object* v_attrKind_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_58_ = lean_unsigned_to_nat(1u);
v_attrKind_59_ = l_Lean_Syntax_getArg(v_x_51_, v___x_58_);
v___x_60_ = ((lean_object*)(l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4));
lean_inc(v_attrKind_59_);
v___x_61_ = l_Lean_Syntax_isOfKind(v_attrKind_59_, v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_attrKind_59_);
lean_dec(v_visibility_x3f_55_);
lean_dec(v_x_51_);
v___x_62_ = l_Lean_Fmt_Error_partialFormatter;
v___x_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___y_57_);
return v___x_63_;
}
else
{
lean_object* v___x_64_; lean_object* v_keywordTk_65_; lean_object* v___x_66_; lean_object* v_type_67_; 
v___x_64_ = lean_unsigned_to_nat(2u);
v_keywordTk_65_ = l_Lean_Syntax_getArg(v_x_51_, v___x_64_);
v___x_66_ = lean_unsigned_to_nat(3u);
v_type_67_ = l_Lean_Syntax_getArg(v_x_51_, v___x_66_);
lean_dec(v_x_51_);
if (lean_obj_tag(v_visibility_x3f_55_) == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_box(0);
v___x_69_ = l_Lean_Fmt_fmtEnsureEvalInstance(v___x_68_, v_attrKind_59_, v_keywordTk_65_, v_type_67_, v___y_56_, v___y_57_);
return v___x_69_;
}
else
{
lean_object* v_val_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_78_; 
v_val_70_ = lean_ctor_get(v_visibility_x3f_55_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v_visibility_x3f_55_);
if (v_isSharedCheck_78_ == 0)
{
v___x_72_ = v_visibility_x3f_55_;
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_val_70_);
lean_dec(v_visibility_x3f_55_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_75_; 
if (v_isShared_73_ == 0)
{
v___x_75_ = v___x_72_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_val_70_);
v___x_75_ = v_reuseFailAlloc_77_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Fmt_fmtEnsureEvalInstance(v___x_75_, v_attrKind_59_, v_keywordTk_65_, v_type_67_, v___y_56_, v___y_57_);
return v___x_76_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalTermInstance___boxed(lean_object* v_x_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Fmt_fmtEnsureEvalTermInstance(v_x_93_, v_a_94_, v_a_95_);
lean_dec_ref(v_a_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1(){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_104_ = l_Lean_Fmt_fmtAttribute;
v___x_105_ = ((lean_object*)(l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__8));
v___x_106_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___closed__2));
v___x_107_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtEnsureEvalTermInstance___boxed), 3, 0);
v___x_108_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_104_, v___x_105_, v___x_106_, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1___boxed(lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1();
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalExprInstance(lean_object* v_x_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_visibility_x3f_121_; lean_object* v___y_122_; lean_object* v___y_123_; lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_145_ = ((lean_object*)(l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__1));
lean_inc(v_x_117_);
v___x_146_ = l_Lean_Syntax_isOfKind(v_x_117_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_x_117_);
v___x_147_ = l_Lean_Fmt_Error_partialFormatter;
v___x_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v_a_119_);
return v___x_148_;
}
else
{
lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = l_Lean_Syntax_getArg(v_x_117_, v___x_149_);
v___x_151_ = l_Lean_Syntax_isNone(v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_150_);
v___x_153_ = l_Lean_Syntax_matchesNull(v___x_150_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v___x_150_);
lean_dec(v_x_117_);
v___x_154_ = l_Lean_Fmt_Error_partialFormatter;
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_a_119_);
return v___x_155_;
}
else
{
lean_object* v_visibility_x3f_156_; lean_object* v___x_157_; 
v_visibility_x3f_156_ = l_Lean_Syntax_getArg(v___x_150_, v___x_149_);
lean_dec(v___x_150_);
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v_visibility_x3f_156_);
v_visibility_x3f_121_ = v___x_157_;
v___y_122_ = v_a_118_;
v___y_123_ = v_a_119_;
goto v___jp_120_;
}
}
else
{
lean_object* v___x_158_; 
lean_dec(v___x_150_);
v___x_158_ = lean_box(0);
v_visibility_x3f_121_ = v___x_158_;
v___y_122_ = v_a_118_;
v___y_123_ = v_a_119_;
goto v___jp_120_;
}
}
v___jp_120_:
{
lean_object* v___x_124_; lean_object* v_attrKind_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v_attrKind_125_ = l_Lean_Syntax_getArg(v_x_117_, v___x_124_);
v___x_126_ = ((lean_object*)(l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4));
lean_inc(v_attrKind_125_);
v___x_127_ = l_Lean_Syntax_isOfKind(v_attrKind_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_attrKind_125_);
lean_dec(v_visibility_x3f_121_);
lean_dec(v_x_117_);
v___x_128_ = l_Lean_Fmt_Error_partialFormatter;
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___y_123_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v_keywordTk_131_; lean_object* v___x_132_; lean_object* v_type_133_; 
v___x_130_ = lean_unsigned_to_nat(2u);
v_keywordTk_131_ = l_Lean_Syntax_getArg(v_x_117_, v___x_130_);
v___x_132_ = lean_unsigned_to_nat(3u);
v_type_133_ = l_Lean_Syntax_getArg(v_x_117_, v___x_132_);
lean_dec(v_x_117_);
if (lean_obj_tag(v_visibility_x3f_121_) == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_box(0);
v___x_135_ = l_Lean_Fmt_fmtEnsureEvalInstance(v___x_134_, v_attrKind_125_, v_keywordTk_131_, v_type_133_, v___y_122_, v___y_123_);
return v___x_135_;
}
else
{
lean_object* v_val_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_144_; 
v_val_136_ = lean_ctor_get(v_visibility_x3f_121_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v_visibility_x3f_121_);
if (v_isSharedCheck_144_ == 0)
{
v___x_138_ = v_visibility_x3f_121_;
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_val_136_);
lean_dec(v_visibility_x3f_121_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_val_136_);
v___x_141_ = v_reuseFailAlloc_143_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Fmt_fmtEnsureEvalInstance(v___x_141_, v_attrKind_125_, v_keywordTk_131_, v_type_133_, v___y_122_, v___y_123_);
return v___x_142_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalExprInstance___boxed(lean_object* v_x_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Fmt_fmtEnsureEvalExprInstance(v_x_159_, v_a_160_, v_a_161_);
lean_dec_ref(v_a_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1(){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_169_ = l_Lean_Fmt_fmtAttribute;
v___x_170_ = ((lean_object*)(l_Lean_Fmt_fmtEnsureEvalExprInstance___closed__1));
v___x_171_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___closed__1));
v___x_172_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtEnsureEvalExprInstance___boxed), 3, 0);
v___x_173_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_169_, v___x_170_, v___x_171_, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1___boxed(lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1();
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalTermExprInstances(lean_object* v_x_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_visibility_x3f_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__1));
lean_inc(v_x_182_);
v___x_211_ = l_Lean_Syntax_isOfKind(v_x_182_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v_x_182_);
v___x_212_ = l_Lean_Fmt_Error_partialFormatter;
v___x_213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v_a_184_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = l_Lean_Syntax_getArg(v_x_182_, v___x_214_);
v___x_216_ = l_Lean_Syntax_isNone(v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_215_);
v___x_218_ = l_Lean_Syntax_matchesNull(v___x_215_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v___x_215_);
lean_dec(v_x_182_);
v___x_219_ = l_Lean_Fmt_Error_partialFormatter;
v___x_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v_a_184_);
return v___x_220_;
}
else
{
lean_object* v_visibility_x3f_221_; lean_object* v___x_222_; 
v_visibility_x3f_221_ = l_Lean_Syntax_getArg(v___x_215_, v___x_214_);
lean_dec(v___x_215_);
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v_visibility_x3f_221_);
v_visibility_x3f_186_ = v___x_222_;
v___y_187_ = v_a_183_;
v___y_188_ = v_a_184_;
goto v___jp_185_;
}
}
else
{
lean_object* v___x_223_; 
lean_dec(v___x_215_);
v___x_223_ = lean_box(0);
v_visibility_x3f_186_ = v___x_223_;
v___y_187_ = v_a_183_;
v___y_188_ = v_a_184_;
goto v___jp_185_;
}
}
v___jp_185_:
{
lean_object* v___x_189_; lean_object* v_attrKind_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_189_ = lean_unsigned_to_nat(1u);
v_attrKind_190_ = l_Lean_Syntax_getArg(v_x_182_, v___x_189_);
v___x_191_ = ((lean_object*)(l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4));
lean_inc(v_attrKind_190_);
v___x_192_ = l_Lean_Syntax_isOfKind(v_attrKind_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_attrKind_190_);
lean_dec(v_visibility_x3f_186_);
lean_dec(v_x_182_);
v___x_193_ = l_Lean_Fmt_Error_partialFormatter;
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___y_188_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v_keywordTk_196_; lean_object* v___x_197_; lean_object* v_type_198_; 
v___x_195_ = lean_unsigned_to_nat(2u);
v_keywordTk_196_ = l_Lean_Syntax_getArg(v_x_182_, v___x_195_);
v___x_197_ = lean_unsigned_to_nat(3u);
v_type_198_ = l_Lean_Syntax_getArg(v_x_182_, v___x_197_);
lean_dec(v_x_182_);
if (lean_obj_tag(v_visibility_x3f_186_) == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_box(0);
v___x_200_ = l_Lean_Fmt_fmtEnsureEvalInstance(v___x_199_, v_attrKind_190_, v_keywordTk_196_, v_type_198_, v___y_187_, v___y_188_);
return v___x_200_;
}
else
{
lean_object* v_val_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_209_; 
v_val_201_ = lean_ctor_get(v_visibility_x3f_186_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v_visibility_x3f_186_);
if (v_isSharedCheck_209_ == 0)
{
v___x_203_ = v_visibility_x3f_186_;
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_val_201_);
lean_dec(v_visibility_x3f_186_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_val_201_);
v___x_206_ = v_reuseFailAlloc_208_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Fmt_fmtEnsureEvalInstance(v___x_206_, v_attrKind_190_, v_keywordTk_196_, v_type_198_, v___y_187_, v___y_188_);
return v___x_207_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEnsureEvalTermExprInstances___boxed(lean_object* v_x_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Fmt_fmtEnsureEvalTermExprInstances(v_x_224_, v_a_225_, v_a_226_);
lean_dec_ref(v_a_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1(){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_234_ = l_Lean_Fmt_fmtAttribute;
v___x_235_ = ((lean_object*)(l_Lean_Fmt_fmtEnsureEvalTermExprInstances___closed__1));
v___x_236_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___closed__1));
v___x_237_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtEnsureEvalTermExprInstances___boxed), 3, 0);
v___x_238_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_234_, v___x_235_, v___x_236_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1___boxed(lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1();
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeriveEvalExprUsingMeta(lean_object* v_x_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_visibility_x3f_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = ((lean_object*)(l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__1));
lean_inc(v_x_247_);
v___x_276_ = l_Lean_Syntax_isOfKind(v_x_247_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec(v_x_247_);
v___x_277_ = l_Lean_Fmt_Error_partialFormatter;
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_a_249_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = l_Lean_Syntax_getArg(v_x_247_, v___x_279_);
v___x_281_ = l_Lean_Syntax_isNone(v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_280_);
v___x_283_ = l_Lean_Syntax_matchesNull(v___x_280_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
lean_dec(v___x_280_);
lean_dec(v_x_247_);
v___x_284_ = l_Lean_Fmt_Error_partialFormatter;
v___x_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v_a_249_);
return v___x_285_;
}
else
{
lean_object* v_visibility_x3f_286_; lean_object* v___x_287_; 
v_visibility_x3f_286_ = l_Lean_Syntax_getArg(v___x_280_, v___x_279_);
lean_dec(v___x_280_);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v_visibility_x3f_286_);
v_visibility_x3f_251_ = v___x_287_;
v___y_252_ = v_a_248_;
v___y_253_ = v_a_249_;
goto v___jp_250_;
}
}
else
{
lean_object* v___x_288_; 
lean_dec(v___x_280_);
v___x_288_ = lean_box(0);
v_visibility_x3f_251_ = v___x_288_;
v___y_252_ = v_a_248_;
v___y_253_ = v_a_249_;
goto v___jp_250_;
}
}
v___jp_250_:
{
lean_object* v___x_254_; lean_object* v_attrKind_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_254_ = lean_unsigned_to_nat(1u);
v_attrKind_255_ = l_Lean_Syntax_getArg(v_x_247_, v___x_254_);
v___x_256_ = ((lean_object*)(l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4));
lean_inc(v_attrKind_255_);
v___x_257_ = l_Lean_Syntax_isOfKind(v_attrKind_255_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v_attrKind_255_);
lean_dec(v_visibility_x3f_251_);
lean_dec(v_x_247_);
v___x_258_ = l_Lean_Fmt_Error_partialFormatter;
v___x_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___y_253_);
return v___x_259_;
}
else
{
lean_object* v___x_260_; lean_object* v_keywordTk_261_; lean_object* v___x_262_; lean_object* v_type_263_; 
v___x_260_ = lean_unsigned_to_nat(2u);
v_keywordTk_261_ = l_Lean_Syntax_getArg(v_x_247_, v___x_260_);
v___x_262_ = lean_unsigned_to_nat(3u);
v_type_263_ = l_Lean_Syntax_getArg(v_x_247_, v___x_262_);
lean_dec(v_x_247_);
if (lean_obj_tag(v_visibility_x3f_251_) == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_box(0);
v___x_265_ = l_Lean_Fmt_fmtEnsureEvalInstance(v___x_264_, v_attrKind_255_, v_keywordTk_261_, v_type_263_, v___y_252_, v___y_253_);
return v___x_265_;
}
else
{
lean_object* v_val_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_274_; 
v_val_266_ = lean_ctor_get(v_visibility_x3f_251_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v_visibility_x3f_251_);
if (v_isSharedCheck_274_ == 0)
{
v___x_268_ = v_visibility_x3f_251_;
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_val_266_);
lean_dec(v_visibility_x3f_251_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_val_266_);
v___x_271_ = v_reuseFailAlloc_273_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Fmt_fmtEnsureEvalInstance(v___x_271_, v_attrKind_255_, v_keywordTk_261_, v_type_263_, v___y_252_, v___y_253_);
return v___x_272_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___boxed(lean_object* v_x_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Fmt_fmtDeriveEvalExprUsingMeta(v_x_289_, v_a_290_, v_a_291_);
lean_dec_ref(v_a_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1(){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_299_ = l_Lean_Fmt_fmtAttribute;
v___x_300_ = ((lean_object*)(l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___closed__1));
v___x_301_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___closed__1));
v___x_302_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDeriveEvalExprUsingMeta___boxed), 3, 0);
v___x_303_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_299_, v___x_300_, v___x_301_, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1___boxed(lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1();
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryOmit(lean_object* v_x_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryOmit___closed__1));
lean_inc(v_x_313_);
v___x_317_ = l_Lean_Syntax_isOfKind(v_x_313_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_x_313_);
v___x_318_ = l_Lean_Fmt_Error_partialFormatter;
v___x_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_a_315_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; lean_object* v_omitTk_321_; lean_object* v___x_322_; 
v___x_320_ = lean_unsigned_to_nat(0u);
v_omitTk_321_ = l_Lean_Syntax_getArg(v_x_313_, v___x_320_);
v___x_322_ = l_Lean_Fmt_fmt(v_omitTk_321_, v_a_314_, v_a_315_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v_a_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_fields_327_; lean_object* v___x_328_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
v_a_324_ = lean_ctor_get(v___x_322_, 1);
lean_inc(v_a_324_);
lean_dec_ref_known(v___x_322_, 2);
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = l_Lean_Syntax_getArg(v_x_313_, v___x_325_);
lean_dec(v_x_313_);
v_fields_327_ = l_Lean_Syntax_getArgs(v___x_326_);
lean_dec(v___x_326_);
v___x_328_ = l_Lean_Fmt_fmtTSepArray___redArg(v_fields_327_, v_a_314_, v_a_324_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_340_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_a_330_ = lean_ctor_get(v___x_328_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_340_ == 0)
{
v___x_332_ = v___x_328_;
v_isShared_333_ = v_isSharedCheck_340_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_340_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_334_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryOmit___closed__2));
v___x_335_ = 1;
v___x_336_ = l_Lean_Fmt_Layouts_keywordPrefixedSepFill(v___x_334_, v_a_323_, v_a_329_, v___x_335_);
lean_dec(v_a_329_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_336_);
v___x_338_ = v___x_332_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_a_330_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
else
{
lean_object* v_a_341_; lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_a_323_);
v_a_341_ = lean_ctor_get(v___x_328_, 0);
v_a_342_ = lean_ctor_get(v___x_328_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_328_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_inc(v_a_341_);
lean_dec(v___x_328_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_341_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_dec(v_x_313_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryOmit___boxed(lean_object* v_x_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Fmt_fmtConfigEntryOmit(v_x_350_, v_a_351_, v_a_352_);
lean_dec_ref(v_a_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1(){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_360_ = l_Lean_Fmt_fmtAttribute;
v___x_361_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryOmit___closed__1));
v___x_362_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___closed__1));
v___x_363_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConfigEntryOmit___boxed), 3, 0);
v___x_364_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_360_, v___x_361_, v___x_362_, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1___boxed(lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1();
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix(lean_object* v_x_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__1));
lean_inc(v_x_376_);
v___x_380_ = l_Lean_Syntax_isOfKind(v_x_376_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec(v_x_376_);
v___x_381_ = l_Lean_Fmt_Error_partialFormatter;
v___x_382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v_a_378_);
return v___x_382_;
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v_dotTk_x3f_386_; lean_object* v_starTk_x3f_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = l_Lean_Syntax_getArg(v_x_376_, v___x_383_);
v___x_412_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__3));
lean_inc(v___x_384_);
v___x_413_ = l_Lean_Syntax_isOfKind(v___x_384_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec(v___x_384_);
lean_dec(v_x_376_);
v___x_414_ = l_Lean_Fmt_Error_partialFormatter;
v___x_415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v_a_378_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = l_Lean_Syntax_getArg(v_x_376_, v___x_416_);
lean_dec(v_x_376_);
v___x_418_ = l_Lean_Syntax_isNone(v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_419_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_417_);
v___x_420_ = l_Lean_Syntax_matchesNull(v___x_417_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec(v___x_417_);
lean_dec(v___x_384_);
v___x_421_ = l_Lean_Fmt_Error_partialFormatter;
v___x_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v_a_378_);
return v___x_422_;
}
else
{
lean_object* v_dotTk_x3f_423_; lean_object* v_starTk_x3f_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_dotTk_x3f_423_ = l_Lean_Syntax_getArg(v___x_417_, v___x_383_);
v_starTk_x3f_424_ = l_Lean_Syntax_getArg(v___x_417_, v___x_416_);
lean_dec(v___x_417_);
v___x_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_425_, 0, v_dotTk_x3f_423_);
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v_starTk_x3f_424_);
v_dotTk_x3f_386_ = v___x_425_;
v_starTk_x3f_387_ = v___x_426_;
v___y_388_ = v_a_377_;
v___y_389_ = v_a_378_;
goto v___jp_385_;
}
}
else
{
lean_object* v___x_427_; 
lean_dec(v___x_417_);
v___x_427_ = lean_box(0);
v_dotTk_x3f_386_ = v___x_427_;
v_starTk_x3f_387_ = v___x_427_;
v___y_388_ = v_a_377_;
v___y_389_ = v_a_378_;
goto v___jp_385_;
}
}
v___jp_385_:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Fmt_fmt(v___x_384_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v_a_392_; lean_object* v___x_393_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
v_a_392_ = lean_ctor_get(v___x_390_, 1);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_390_, 2);
v___x_393_ = l_Lean_Fmt_fmt_x3f(v_dotTk_x3f_386_, v___y_388_, v_a_392_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v_a_395_; lean_object* v___x_396_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
v_a_395_ = lean_ctor_get(v___x_393_, 1);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_393_, 2);
v___x_396_ = l_Lean_Fmt_fmt_x3f(v_starTk_x3f_387_, v___y_388_, v_a_395_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_411_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_a_398_ = lean_ctor_get(v___x_396_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_411_ == 0)
{
v___x_400_ = v___x_396_;
v_isShared_401_ = v_isSharedCheck_411_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_411_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_402_ = lean_unsigned_to_nat(3u);
v___x_403_ = lean_mk_empty_array_with_capacity(v___x_402_);
v___x_404_ = lean_array_push(v___x_403_, v_a_391_);
v___x_405_ = lean_array_push(v___x_404_, v_a_394_);
v___x_406_ = lean_array_push(v___x_405_, v_a_397_);
v___x_407_ = l_Lean_Fmt_Layouts_atomic(v___x_406_);
lean_dec_ref(v___x_406_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_407_);
v___x_409_ = v___x_400_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_a_398_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_dec(v_a_394_);
lean_dec(v_a_391_);
return v___x_396_;
}
}
else
{
lean_dec(v_a_391_);
lean_dec(v_starTk_x3f_387_);
return v___x_393_;
}
}
else
{
lean_dec(v_starTk_x3f_387_);
lean_dec(v_dotTk_x3f_386_);
return v___x_390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___boxed(lean_object* v_x_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix(v_x_428_, v_a_429_, v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1(){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_438_ = l_Lean_Fmt_fmtAttribute;
v___x_439_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__1));
v___x_440_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___closed__1));
v___x_441_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___boxed), 3, 0);
v___x_442_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_438_, v___x_439_, v___x_440_, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1___boxed(lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1();
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKey(lean_object* v_x_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__1));
lean_inc(v_x_457_);
v___x_461_ = l_Lean_Syntax_isOfKind(v_x_457_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec(v_x_457_);
v___x_462_ = l_Lean_Fmt_Error_partialFormatter;
v___x_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v_a_459_);
return v___x_463_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = l_Lean_Syntax_getArg(v_x_457_, v___x_464_);
lean_dec(v_x_457_);
v___x_466_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__1));
lean_inc(v___x_465_);
v___x_467_ = l_Lean_Syntax_isOfKind(v___x_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__3));
lean_inc(v___x_465_);
v___x_469_ = l_Lean_Syntax_isOfKind(v___x_465_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec(v___x_465_);
v___x_470_ = l_Lean_Fmt_Error_partialFormatter;
v___x_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v_a_459_);
return v___x_471_;
}
else
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_Fmt_fmt(v___x_465_, v_a_458_, v_a_459_);
return v___x_472_;
}
}
else
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_Fmt_fmt(v___x_465_, v_a_458_, v_a_459_);
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryHandlerKey___boxed(lean_object* v_x_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Fmt_fmtConfigEntryHandlerKey(v_x_474_, v_a_475_, v_a_476_);
lean_dec_ref(v_a_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1(){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_484_ = l_Lean_Fmt_fmtAttribute;
v___x_485_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__1));
v___x_486_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___closed__1));
v___x_487_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConfigEntryHandlerKey___boxed), 3, 0);
v___x_488_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_484_, v___x_485_, v___x_486_, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1___boxed(lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1();
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryHandler(lean_object* v_x_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandler___closed__1));
lean_inc(v_x_497_);
v___x_501_ = l_Lean_Syntax_isOfKind(v_x_497_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v_x_497_);
v___x_502_ = l_Lean_Fmt_Error_partialFormatter;
v___x_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v_a_499_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = l_Lean_Syntax_getArg(v_x_497_, v___x_504_);
v___x_506_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandlerKey___closed__1));
lean_inc(v___x_505_);
v___x_507_ = l_Lean_Syntax_isOfKind(v___x_505_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v___x_505_);
lean_dec(v_x_497_);
v___x_508_ = l_Lean_Fmt_Error_partialFormatter;
v___x_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_a_499_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; lean_object* v_optionTk_511_; lean_object* v___x_512_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v_optionTk_511_ = l_Lean_Syntax_getArg(v_x_497_, v___x_510_);
v___x_512_ = l_Lean_Fmt_fmt(v_optionTk_511_, v_a_498_, v_a_499_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v_a_514_; lean_object* v___x_515_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
v_a_514_ = lean_ctor_get(v___x_512_, 1);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_512_, 2);
v___x_515_ = l_Lean_Fmt_fmt(v___x_505_, v_a_498_, v_a_514_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v_a_517_; lean_object* v___x_518_; lean_object* v_colonEqTk_519_; lean_object* v___x_520_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
v_a_517_ = lean_ctor_get(v___x_515_, 1);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_515_, 2);
v___x_518_ = lean_unsigned_to_nat(2u);
v_colonEqTk_519_ = l_Lean_Syntax_getArg(v_x_497_, v___x_518_);
v___x_520_ = l_Lean_Fmt_fmt(v_colonEqTk_519_, v_a_498_, v_a_517_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v_a_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
v_a_522_ = lean_ctor_get(v___x_520_, 1);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_520_, 2);
v___x_523_ = lean_unsigned_to_nat(3u);
v___x_524_ = l_Lean_Syntax_getArg(v_x_497_, v___x_523_);
lean_dec(v_x_497_);
v___x_525_ = l_Lean_Fmt_fmt(v___x_524_, v_a_498_, v_a_522_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_541_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_a_527_ = lean_ctor_get(v___x_525_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_541_ == 0)
{
v___x_529_ = v___x_525_;
v_isShared_530_ = v_isSharedCheck_541_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_541_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_531_ = lean_mk_empty_array_with_capacity(v___x_518_);
v___x_532_ = lean_array_push(v___x_531_, v_a_513_);
v___x_533_ = lean_array_push(v___x_532_, v_a_516_);
v___x_534_ = 0;
v___x_535_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_535_, 0, v___x_507_);
lean_ctor_set_uint8(v___x_535_, 1, v___x_534_);
lean_ctor_set_uint8(v___x_535_, 2, v___x_534_);
lean_ctor_set_uint8(v___x_535_, 3, v___x_534_);
v___x_536_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_533_, v___x_535_);
v___x_537_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_536_, v_a_521_, v_a_526_, v___x_534_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_537_);
v___x_539_ = v___x_529_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_a_527_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
else
{
lean_dec(v_a_521_);
lean_dec(v_a_516_);
lean_dec(v_a_513_);
return v___x_525_;
}
}
else
{
lean_dec(v_a_516_);
lean_dec(v_a_513_);
lean_dec(v_x_497_);
return v___x_520_;
}
}
else
{
lean_dec(v_a_513_);
lean_dec(v_x_497_);
return v___x_515_;
}
}
else
{
lean_dec(v___x_505_);
lean_dec(v_x_497_);
return v___x_512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntryHandler___boxed(lean_object* v_x_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Fmt_fmtConfigEntryHandler(v_x_542_, v_a_543_, v_a_544_);
lean_dec_ref(v_a_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1(){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_552_ = l_Lean_Fmt_fmtAttribute;
v___x_553_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandler___closed__1));
v___x_554_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___closed__1));
v___x_555_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConfigEntryHandler___boxed), 3, 0);
v___x_556_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_552_, v___x_553_, v___x_554_, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1___boxed(lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1();
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntry(lean_object* v_x_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntry___closed__1));
lean_inc(v_x_565_);
v___x_569_ = l_Lean_Syntax_isOfKind(v_x_565_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v_x_565_);
v___x_570_ = l_Lean_Fmt_Error_partialFormatter;
v___x_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_a_567_);
return v___x_571_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = l_Lean_Syntax_getArg(v_x_565_, v___x_572_);
lean_dec(v_x_565_);
v___x_574_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryOmit___closed__1));
lean_inc(v___x_573_);
v___x_575_ = l_Lean_Syntax_isOfKind(v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandler___closed__1));
lean_inc(v___x_573_);
v___x_577_ = l_Lean_Syntax_isOfKind(v___x_573_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v___x_573_);
v___x_578_ = l_Lean_Fmt_Error_partialFormatter;
v___x_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v_a_567_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Fmt_fmt(v___x_573_, v_a_566_, v_a_567_);
return v___x_580_;
}
}
else
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Fmt_fmt(v___x_573_, v_a_566_, v_a_567_);
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigEntry___boxed(lean_object* v_x_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Fmt_fmtConfigEntry(v_x_582_, v_a_583_, v_a_584_);
lean_dec_ref(v_a_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1(){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_592_ = l_Lean_Fmt_fmtAttribute;
v___x_593_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntry___closed__1));
v___x_594_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___closed__1));
v___x_595_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConfigEntry___boxed), 3, 0);
v___x_596_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_592_, v___x_593_, v___x_594_, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1___boxed(lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1();
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithConfigEntries(lean_object* v_signature_606_, lean_object* v_configEntries_x3f_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
if (lean_obj_tag(v_configEntries_x3f_607_) == 1)
{
lean_object* v_val_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v_val_610_ = lean_ctor_get(v_configEntries_x3f_607_, 0);
lean_inc_n(v_val_610_, 2);
lean_dec_ref_known(v_configEntries_x3f_607_, 1);
v___x_611_ = ((lean_object*)(l_Lean_Fmt_fmtWithConfigEntries___closed__1));
v___x_612_ = l_Lean_Syntax_isOfKind(v_val_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_val_610_);
lean_dec_ref(v_signature_606_);
v___x_613_ = l_Lean_Fmt_Error_partialFormatter;
v___x_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v_a_609_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; lean_object* v_whereTk_616_; lean_object* v___x_617_; 
v___x_615_ = lean_unsigned_to_nat(0u);
v_whereTk_616_ = l_Lean_Syntax_getArg(v_val_610_, v___x_615_);
v___x_617_ = l_Lean_Fmt_fmt(v_whereTk_616_, v_a_608_, v_a_609_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v_a_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_entries_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
v_a_619_ = lean_ctor_get(v___x_617_, 1);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_617_, 2);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = l_Lean_Syntax_getArg(v_val_610_, v___x_620_);
lean_dec(v_val_610_);
v___x_622_ = ((lean_object*)(l_Lean_Fmt_fmtWithConfigEntries___closed__2));
v_entries_623_ = l_Lean_Syntax_getArgs(v___x_621_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v___x_625_ = l_Lean_Fmt_fmtSeq___redArg(v___x_622_, v_entries_623_, v___x_624_, v_a_608_, v_a_619_);
lean_dec_ref(v_entries_623_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_635_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v_a_627_ = lean_ctor_get(v___x_625_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_635_ == 0)
{
v___x_629_ = v___x_625_;
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_inc(v_a_626_);
lean_dec(v___x_625_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = l_Lean_Fmt_Layouts_whereDeclaration(v_signature_606_, v_a_618_, v_a_626_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_a_627_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
lean_dec(v_a_618_);
lean_dec_ref(v_signature_606_);
return v___x_625_;
}
}
else
{
lean_dec(v_val_610_);
lean_dec_ref(v_signature_606_);
return v___x_617_;
}
}
}
else
{
lean_object* v___x_636_; 
lean_dec(v_configEntries_x3f_607_);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v_signature_606_);
lean_ctor_set(v___x_636_, 1, v_a_609_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithConfigEntries___boxed(lean_object* v_signature_637_, lean_object* v_configEntries_x3f_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Fmt_fmtWithConfigEntries(v_signature_637_, v_configEntries_x3f_638_, v_a_639_, v_a_640_);
lean_dec_ref(v_a_639_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDefEvalConfigItemCmd_spec__0(size_t v_sz_642_, size_t v_i_643_, lean_object* v_bs_644_){
_start:
{
uint8_t v___x_645_; 
v___x_645_ = lean_usize_dec_lt(v_i_643_, v_sz_642_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v_bs_644_);
return v___x_646_;
}
else
{
lean_object* v_v_647_; lean_object* v___x_648_; lean_object* v_bs_x27_649_; size_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; 
v_v_647_ = lean_array_uget(v_bs_644_, v_i_643_);
v___x_648_ = lean_unsigned_to_nat(0u);
v_bs_x27_649_ = lean_array_uset(v_bs_644_, v_i_643_, v___x_648_);
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_add(v_i_643_, v___x_650_);
v___x_652_ = lean_array_uset(v_bs_x27_649_, v_i_643_, v_v_647_);
v_i_643_ = v___x_651_;
v_bs_644_ = v___x_652_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDefEvalConfigItemCmd_spec__0___boxed(lean_object* v_sz_654_, lean_object* v_i_655_, lean_object* v_bs_656_){
_start:
{
size_t v_sz_boxed_657_; size_t v_i_boxed_658_; lean_object* v_res_659_; 
v_sz_boxed_657_ = lean_unbox_usize(v_sz_654_);
lean_dec(v_sz_654_);
v_i_boxed_658_ = lean_unbox_usize(v_i_655_);
lean_dec(v_i_655_);
v_res_659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDefEvalConfigItemCmd_spec__0(v_sz_boxed_657_, v_i_boxed_658_, v_bs_656_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDefEvalConfigItemCmd(lean_object* v_x_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___x_690_; uint8_t v___x_691_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v_configEntries_x3f_702_; lean_object* v___y_703_; lean_object* v___y_704_; 
v___x_690_ = ((lean_object*)(l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__1));
lean_inc(v_x_673_);
v___x_691_ = l_Lean_Syntax_isOfKind(v_x_673_, v___x_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec(v_x_673_);
v___x_755_ = l_Lean_Fmt_Error_partialFormatter;
v___x_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v_a_675_);
return v___x_756_;
}
else
{
lean_object* v___x_757_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v_visibility_x3f_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v_docComment_x3f_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_826_ = l_Lean_Syntax_getArg(v_x_673_, v___x_757_);
v___x_827_ = l_Lean_Syntax_isNone(v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_826_);
v___x_829_ = l_Lean_Syntax_matchesNull(v___x_826_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec(v___x_826_);
lean_dec(v_x_673_);
v___x_830_ = l_Lean_Fmt_Error_partialFormatter;
v___x_831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v_a_675_);
return v___x_831_;
}
else
{
lean_object* v_docComment_x3f_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_docComment_x3f_832_ = l_Lean_Syntax_getArg(v___x_826_, v___x_757_);
lean_dec(v___x_826_);
v___x_833_ = ((lean_object*)(l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4));
lean_inc(v_docComment_x3f_832_);
v___x_834_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_832_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec(v_docComment_x3f_832_);
lean_dec(v_x_673_);
v___x_835_ = l_Lean_Fmt_Error_partialFormatter;
v___x_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v_a_675_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; 
v___x_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_837_, 0, v_docComment_x3f_832_);
v_docComment_x3f_814_ = v___x_837_;
v___y_815_ = v_a_674_;
v___y_816_ = v_a_675_;
goto v___jp_813_;
}
}
}
else
{
lean_object* v___x_838_; 
lean_dec(v___x_826_);
v___x_838_ = lean_box(0);
v_docComment_x3f_814_ = v___x_838_;
v___y_815_ = v_a_674_;
v___y_816_ = v_a_675_;
goto v___jp_813_;
}
v___jp_758_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_764_ = lean_unsigned_to_nat(2u);
v___x_765_ = l_Lean_Syntax_getArg(v_x_673_, v___x_764_);
v___x_766_ = ((lean_object*)(l_Lean_Fmt_fmtEnsureEvalTermInstance___closed__4));
lean_inc(v___x_765_);
v___x_767_ = l_Lean_Syntax_isOfKind(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec(v___x_765_);
lean_dec(v_visibility_x3f_761_);
lean_dec(v___y_759_);
lean_dec(v_x_673_);
v___x_768_ = l_Lean_Fmt_Error_partialFormatter;
v___x_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v___y_763_);
return v___x_769_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_770_ = lean_unsigned_to_nat(4u);
v___x_771_ = l_Lean_Syntax_getArg(v_x_673_, v___x_770_);
v___x_772_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__3));
lean_inc(v___x_771_);
v___x_773_ = l_Lean_Syntax_isOfKind(v___x_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v___x_771_);
lean_dec(v___x_765_);
lean_dec(v_visibility_x3f_761_);
lean_dec(v___y_759_);
lean_dec(v_x_673_);
v___x_774_ = l_Lean_Fmt_Error_partialFormatter;
v___x_775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v___y_763_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; size_t v_sz_779_; size_t v___x_780_; lean_object* v___x_781_; 
v___x_776_ = lean_unsigned_to_nat(5u);
v___x_777_ = l_Lean_Syntax_getArg(v_x_673_, v___x_776_);
v___x_778_ = l_Lean_Syntax_getArgs(v___x_777_);
lean_dec(v___x_777_);
v_sz_779_ = lean_array_size(v___x_778_);
v___x_780_ = ((size_t)0ULL);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDefEvalConfigItemCmd_spec__0(v_sz_779_, v___x_780_, v___x_778_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec(v___x_771_);
lean_dec(v___x_765_);
lean_dec(v_visibility_x3f_761_);
lean_dec(v___y_759_);
lean_dec(v_x_673_);
v___x_782_ = l_Lean_Fmt_Error_partialFormatter;
v___x_783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v___y_763_);
return v___x_783_;
}
else
{
lean_object* v_val_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_812_; 
v_val_784_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_812_ == 0)
{
v___x_786_ = v___x_781_;
v_isShared_787_ = v_isSharedCheck_812_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_val_784_);
lean_dec(v___x_781_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_812_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_788_ = lean_unsigned_to_nat(7u);
v___x_789_ = l_Lean_Syntax_getArg(v_x_673_, v___x_788_);
lean_inc(v___x_789_);
v___x_790_ = l_Lean_Syntax_isOfKind(v___x_789_, v___x_772_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec(v___x_789_);
lean_del_object(v___x_786_);
lean_dec(v_val_784_);
lean_dec(v___x_771_);
lean_dec(v___x_765_);
lean_dec(v_visibility_x3f_761_);
lean_dec(v___y_759_);
lean_dec(v_x_673_);
v___x_791_ = l_Lean_Fmt_Error_partialFormatter;
v___x_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___y_763_);
return v___x_792_;
}
else
{
lean_object* v___x_793_; lean_object* v_defTk_794_; lean_object* v___x_795_; lean_object* v_forTk_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_793_ = lean_unsigned_to_nat(3u);
v_defTk_794_ = l_Lean_Syntax_getArg(v_x_673_, v___x_793_);
v___x_795_ = lean_unsigned_to_nat(6u);
v_forTk_796_ = l_Lean_Syntax_getArg(v_x_673_, v___x_795_);
v___x_797_ = lean_unsigned_to_nat(8u);
v___x_798_ = l_Lean_Syntax_getArg(v_x_673_, v___x_797_);
lean_dec(v_x_673_);
v___x_799_ = l_Lean_Syntax_isNone(v___x_798_);
if (v___x_799_ == 0)
{
uint8_t v___x_800_; 
lean_inc(v___x_798_);
v___x_800_ = l_Lean_Syntax_matchesNull(v___x_798_, v___y_760_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec(v___x_798_);
lean_dec(v_forTk_796_);
lean_dec(v_defTk_794_);
lean_dec(v___x_789_);
lean_del_object(v___x_786_);
lean_dec(v_val_784_);
lean_dec(v___x_771_);
lean_dec(v___x_765_);
lean_dec(v_visibility_x3f_761_);
lean_dec(v___y_759_);
v___x_801_ = l_Lean_Fmt_Error_partialFormatter;
v___x_802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v___y_763_);
return v___x_802_;
}
else
{
lean_object* v_configEntries_x3f_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_configEntries_x3f_803_ = l_Lean_Syntax_getArg(v___x_798_, v___x_757_);
lean_dec(v___x_798_);
v___x_804_ = ((lean_object*)(l_Lean_Fmt_fmtWithConfigEntries___closed__1));
lean_inc(v_configEntries_x3f_803_);
v___x_805_ = l_Lean_Syntax_isOfKind(v_configEntries_x3f_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec(v_configEntries_x3f_803_);
lean_dec(v_forTk_796_);
lean_dec(v_defTk_794_);
lean_dec(v___x_789_);
lean_del_object(v___x_786_);
lean_dec(v_val_784_);
lean_dec(v___x_771_);
lean_dec(v___x_765_);
lean_dec(v_visibility_x3f_761_);
lean_dec(v___y_759_);
v___x_806_ = l_Lean_Fmt_Error_partialFormatter;
v___x_807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v___y_763_);
return v___x_807_;
}
else
{
lean_object* v___x_809_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v_configEntries_x3f_803_);
v___x_809_ = v___x_786_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_configEntries_x3f_803_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
v___y_693_ = v___y_759_;
v___y_694_ = v___x_789_;
v___y_695_ = v_val_784_;
v___y_696_ = v_visibility_x3f_761_;
v___y_697_ = v_defTk_794_;
v___y_698_ = v___x_771_;
v___y_699_ = v___x_764_;
v___y_700_ = v___x_765_;
v___y_701_ = v_forTk_796_;
v_configEntries_x3f_702_ = v___x_809_;
v___y_703_ = v___y_762_;
v___y_704_ = v___y_763_;
goto v___jp_692_;
}
}
}
}
else
{
lean_object* v___x_811_; 
lean_dec(v___x_798_);
lean_del_object(v___x_786_);
v___x_811_ = lean_box(0);
v___y_693_ = v___y_759_;
v___y_694_ = v___x_789_;
v___y_695_ = v_val_784_;
v___y_696_ = v_visibility_x3f_761_;
v___y_697_ = v_defTk_794_;
v___y_698_ = v___x_771_;
v___y_699_ = v___x_764_;
v___y_700_ = v___x_765_;
v___y_701_ = v_forTk_796_;
v_configEntries_x3f_702_ = v___x_811_;
v___y_703_ = v___y_762_;
v___y_704_ = v___y_763_;
goto v___jp_692_;
}
}
}
}
}
}
}
v___jp_813_:
{
lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_817_ = lean_unsigned_to_nat(1u);
v___x_818_ = l_Lean_Syntax_getArg(v_x_673_, v___x_817_);
v___x_819_ = l_Lean_Syntax_isNone(v___x_818_);
if (v___x_819_ == 0)
{
uint8_t v___x_820_; 
lean_inc(v___x_818_);
v___x_820_ = l_Lean_Syntax_matchesNull(v___x_818_, v___x_817_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v___x_818_);
lean_dec(v_docComment_x3f_814_);
lean_dec(v_x_673_);
v___x_821_ = l_Lean_Fmt_Error_partialFormatter;
v___x_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___y_816_);
return v___x_822_;
}
else
{
lean_object* v_visibility_x3f_823_; lean_object* v___x_824_; 
v_visibility_x3f_823_ = l_Lean_Syntax_getArg(v___x_818_, v___x_757_);
lean_dec(v___x_818_);
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v_visibility_x3f_823_);
v___y_759_ = v_docComment_x3f_814_;
v___y_760_ = v___x_817_;
v_visibility_x3f_761_ = v___x_824_;
v___y_762_ = v___y_815_;
v___y_763_ = v___y_816_;
goto v___jp_758_;
}
}
else
{
lean_object* v___x_825_; 
lean_dec(v___x_818_);
v___x_825_ = lean_box(0);
v___y_759_ = v_docComment_x3f_814_;
v___y_760_ = v___x_817_;
v_visibility_x3f_761_ = v___x_825_;
v___y_762_ = v___y_815_;
v___y_763_ = v___y_816_;
goto v___jp_758_;
}
}
}
v___jp_676_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v___y_681_);
v___x_686_ = lean_mk_empty_array_with_capacity(v___y_678_);
v___x_687_ = lean_array_push(v___x_686_, v___y_684_);
v___x_688_ = lean_array_push(v___x_687_, v___x_685_);
v___x_689_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_677_, v___y_683_, v___x_688_, v___y_682_, v___y_679_, v___y_680_);
lean_dec_ref(v___x_688_);
return v___x_689_;
}
v___jp_692_:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Fmt_fmt(v___y_697_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v_a_707_; lean_object* v___x_708_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
v_a_707_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_705_, 2);
v___x_708_ = l_Lean_Fmt_fmt(v___y_698_, v___y_703_, v_a_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
v_a_710_ = lean_ctor_get(v___x_708_, 1);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_708_, 2);
v___x_711_ = l_Lean_Fmt_convertBracketedBinders(v___y_695_);
v___x_712_ = l_Lean_Fmt_fmtBinders(v___x_711_, v___y_703_, v_a_710_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v_a_714_; lean_object* v___x_715_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
v_a_714_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_a_714_);
lean_dec_ref_known(v___x_712_, 2);
v___x_715_ = l_Lean_Fmt_fmt(v___y_701_, v___y_703_, v_a_714_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v_a_717_; lean_object* v___x_718_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
v_a_717_ = lean_ctor_get(v___x_715_, 1);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_715_, 2);
v___x_718_ = l_Lean_Fmt_fmt(v___y_694_, v___y_703_, v_a_717_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v_a_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
v_a_720_ = lean_ctor_get(v___x_718_, 1);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_718_, 2);
v___x_721_ = lean_mk_empty_array_with_capacity(v___y_699_);
lean_inc_ref(v___x_721_);
v___x_722_ = lean_array_push(v___x_721_, v_a_706_);
v___x_723_ = lean_array_push(v___x_722_, v_a_709_);
v___x_724_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_725_ = l_Lean_Fmt_Layouts_globalSignature(v___x_723_, v_a_713_, v___x_724_, v___x_724_);
lean_dec(v_a_713_);
lean_dec_ref(v___x_723_);
v___x_726_ = 1;
v___x_727_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_a_716_, v_a_719_, v___x_726_);
v___x_728_ = 0;
v___x_729_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_729_, 0, v___x_725_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*1, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_730_, 0, v___x_727_);
lean_ctor_set_uint8(v___x_730_, sizeof(void*)*1, v___x_691_);
v___x_731_ = lean_array_push(v___x_721_, v___x_729_);
v___x_732_ = lean_array_push(v___x_731_, v___x_730_);
v___x_733_ = l_Lean_Fmt_Layouts_blocks(v___x_732_, v___x_691_);
lean_dec_ref(v___x_732_);
v___x_734_ = l_Lean_Fmt_fmtWithConfigEntries(v___x_733_, v_configEntries_x3f_702_, v___y_703_, v_a_720_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v_a_736_; lean_object* v___x_737_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
v_a_736_ = lean_ctor_get(v___x_734_, 1);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_734_, 2);
v___x_737_ = lean_box(0);
if (lean_obj_tag(v___y_696_) == 0)
{
v___y_677_ = v___y_693_;
v___y_678_ = v___y_699_;
v___y_679_ = v___y_703_;
v___y_680_ = v_a_736_;
v___y_681_ = v___y_700_;
v___y_682_ = v_a_735_;
v___y_683_ = v___x_737_;
v___y_684_ = v___x_737_;
goto v___jp_676_;
}
else
{
lean_object* v_val_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_val_738_ = lean_ctor_get(v___y_696_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___y_696_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___y_696_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_val_738_);
lean_dec(v___y_696_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_val_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
v___y_677_ = v___y_693_;
v___y_678_ = v___y_699_;
v___y_679_ = v___y_703_;
v___y_680_ = v_a_736_;
v___y_681_ = v___y_700_;
v___y_682_ = v_a_735_;
v___y_683_ = v___x_737_;
v___y_684_ = v___x_743_;
goto v___jp_676_;
}
}
}
}
else
{
lean_dec(v___y_700_);
lean_dec(v___y_696_);
lean_dec(v___y_693_);
return v___x_734_;
}
}
else
{
lean_dec(v_a_716_);
lean_dec(v_a_713_);
lean_dec(v_a_709_);
lean_dec(v_a_706_);
lean_dec(v_configEntries_x3f_702_);
lean_dec(v___y_700_);
lean_dec(v___y_696_);
lean_dec(v___y_693_);
return v___x_718_;
}
}
else
{
lean_dec(v_a_713_);
lean_dec(v_a_709_);
lean_dec(v_a_706_);
lean_dec(v_configEntries_x3f_702_);
lean_dec(v___y_700_);
lean_dec(v___y_696_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
return v___x_715_;
}
}
else
{
lean_object* v_a_746_; lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_a_709_);
lean_dec(v_a_706_);
lean_dec(v_configEntries_x3f_702_);
lean_dec(v___y_701_);
lean_dec(v___y_700_);
lean_dec(v___y_696_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
v_a_746_ = lean_ctor_get(v___x_712_, 0);
v_a_747_ = lean_ctor_get(v___x_712_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_712_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_inc(v_a_746_);
lean_dec(v___x_712_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_746_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_dec(v_a_706_);
lean_dec(v_configEntries_x3f_702_);
lean_dec(v___y_701_);
lean_dec(v___y_700_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
return v___x_708_;
}
}
else
{
lean_dec(v_configEntries_x3f_702_);
lean_dec(v___y_701_);
lean_dec(v___y_700_);
lean_dec(v___y_698_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDefEvalConfigItemCmd___boxed(lean_object* v_x_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Fmt_fmtDefEvalConfigItemCmd(v_x_839_, v_a_840_, v_a_841_);
lean_dec_ref(v_a_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1(){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_849_ = l_Lean_Fmt_fmtAttribute;
v___x_850_ = ((lean_object*)(l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__1));
v___x_851_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___closed__1));
v___x_852_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDefEvalConfigItemCmd___boxed), 3, 0);
v___x_853_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_849_, v___x_850_, v___x_851_, v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1___boxed(lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1();
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareConfig(lean_object* v_docComment_x3f_856_, lean_object* v_visibility_x3f_857_, lean_object* v_declTk_858_, lean_object* v_elabId_859_, lean_object* v_structId_860_, lean_object* v_binders_861_, lean_object* v_configEntries_x3f_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Fmt_fmt(v_declTk_858_, v_a_863_, v_a_864_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v_a_867_; lean_object* v___x_868_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
v_a_867_ = lean_ctor_get(v___x_865_, 1);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_865_, 2);
v___x_868_ = l_Lean_Fmt_fmt(v_elabId_859_, v_a_863_, v_a_867_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v_a_870_; lean_object* v___x_871_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
v_a_870_ = lean_ctor_get(v___x_868_, 1);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_868_, 2);
v___x_871_ = l_Lean_Fmt_fmt(v_structId_860_, v_a_863_, v_a_870_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
v_a_873_ = lean_ctor_get(v___x_871_, 1);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_871_, 2);
v___x_874_ = l_Lean_Fmt_convertBracketedBinders(v_binders_861_);
v___x_875_ = l_Lean_Fmt_fmtBinders(v___x_874_, v_a_863_, v_a_873_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v_a_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
v_a_877_ = lean_ctor_get(v___x_875_, 1);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_875_, 2);
v___x_878_ = lean_unsigned_to_nat(3u);
v___x_879_ = lean_mk_empty_array_with_capacity(v___x_878_);
v___x_880_ = lean_array_push(v___x_879_, v_a_866_);
v___x_881_ = lean_array_push(v___x_880_, v_a_869_);
v___x_882_ = lean_array_push(v___x_881_, v_a_872_);
v___x_883_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_884_ = l_Lean_Fmt_Layouts_globalSignature(v___x_882_, v_a_876_, v___x_883_, v___x_883_);
lean_dec(v_a_876_);
lean_dec_ref(v___x_882_);
v___x_885_ = l_Lean_Fmt_fmtWithConfigEntries(v___x_884_, v_configEntries_x3f_862_, v_a_863_, v_a_877_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v_a_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
v_a_887_ = lean_ctor_get(v___x_885_, 1);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_885_, 2);
v___x_888_ = lean_box(0);
v___x_889_ = lean_unsigned_to_nat(1u);
v___x_890_ = lean_mk_empty_array_with_capacity(v___x_889_);
v___x_891_ = lean_array_push(v___x_890_, v_visibility_x3f_857_);
v___x_892_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_856_, v___x_888_, v___x_891_, v_a_886_, v_a_863_, v_a_887_);
lean_dec_ref(v___x_891_);
return v___x_892_;
}
else
{
lean_dec(v_visibility_x3f_857_);
lean_dec(v_docComment_x3f_856_);
return v___x_885_;
}
}
else
{
lean_object* v_a_893_; lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v_a_872_);
lean_dec(v_a_869_);
lean_dec(v_a_866_);
lean_dec(v_configEntries_x3f_862_);
lean_dec(v_visibility_x3f_857_);
lean_dec(v_docComment_x3f_856_);
v_a_893_ = lean_ctor_get(v___x_875_, 0);
v_a_894_ = lean_ctor_get(v___x_875_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_875_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_inc(v_a_893_);
lean_dec(v___x_875_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_893_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_dec(v_a_869_);
lean_dec(v_a_866_);
lean_dec(v_configEntries_x3f_862_);
lean_dec_ref(v_binders_861_);
lean_dec(v_visibility_x3f_857_);
lean_dec(v_docComment_x3f_856_);
return v___x_871_;
}
}
else
{
lean_dec(v_a_866_);
lean_dec(v_configEntries_x3f_862_);
lean_dec_ref(v_binders_861_);
lean_dec(v_structId_860_);
lean_dec(v_visibility_x3f_857_);
lean_dec(v_docComment_x3f_856_);
return v___x_868_;
}
}
else
{
lean_dec(v_configEntries_x3f_862_);
lean_dec_ref(v_binders_861_);
lean_dec(v_structId_860_);
lean_dec(v_elabId_859_);
lean_dec(v_visibility_x3f_857_);
lean_dec(v_docComment_x3f_856_);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareConfig___boxed(lean_object* v_docComment_x3f_902_, lean_object* v_visibility_x3f_903_, lean_object* v_declTk_904_, lean_object* v_elabId_905_, lean_object* v_structId_906_, lean_object* v_binders_907_, lean_object* v_configEntries_x3f_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Fmt_fmtDeclareConfig(v_docComment_x3f_902_, v_visibility_x3f_903_, v_declTk_904_, v_elabId_905_, v_structId_906_, v_binders_907_, v_configEntries_x3f_908_, v_a_909_, v_a_910_);
lean_dec_ref(v_a_909_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareCoreConfigElab(lean_object* v_x_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v_configEntries_x3f_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__1));
lean_inc(v_x_918_);
v___x_943_ = l_Lean_Syntax_isOfKind(v_x_918_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v_x_918_);
v___x_944_ = l_Lean_Fmt_Error_partialFormatter;
v___x_945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v_a_920_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v_visibility_x3f_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v_docComment_x3f_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_1007_ = l_Lean_Syntax_getArg(v_x_918_, v___x_946_);
v___x_1008_ = l_Lean_Syntax_isNone(v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1009_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1007_);
v___x_1010_ = l_Lean_Syntax_matchesNull(v___x_1007_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec(v___x_1007_);
lean_dec(v_x_918_);
v___x_1011_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_a_920_);
return v___x_1012_;
}
else
{
lean_object* v_docComment_x3f_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v_docComment_x3f_1013_ = l_Lean_Syntax_getArg(v___x_1007_, v___x_946_);
lean_dec(v___x_1007_);
v___x_1014_ = ((lean_object*)(l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4));
lean_inc(v_docComment_x3f_1013_);
v___x_1015_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec(v_docComment_x3f_1013_);
lean_dec(v_x_918_);
v___x_1016_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v_a_920_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_docComment_x3f_1013_);
v_docComment_x3f_995_ = v___x_1018_;
v___y_996_ = v_a_919_;
v___y_997_ = v_a_920_;
goto v___jp_994_;
}
}
}
else
{
lean_object* v___x_1019_; 
lean_dec(v___x_1007_);
v___x_1019_ = lean_box(0);
v_docComment_x3f_995_ = v___x_1019_;
v___y_996_ = v_a_919_;
v___y_997_ = v_a_920_;
goto v___jp_994_;
}
v___jp_947_:
{
lean_object* v___x_953_; lean_object* v_elabId_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_953_ = lean_unsigned_to_nat(3u);
v_elabId_954_ = l_Lean_Syntax_getArg(v_x_918_, v___x_953_);
v___x_955_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__3));
lean_inc(v_elabId_954_);
v___x_956_ = l_Lean_Syntax_isOfKind(v_elabId_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_elabId_954_);
lean_dec(v_visibility_x3f_950_);
lean_dec(v___y_949_);
lean_dec(v_x_918_);
v___x_957_ = l_Lean_Fmt_Error_partialFormatter;
v___x_958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v___y_952_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; lean_object* v_structId_960_; uint8_t v___x_961_; 
v___x_959_ = lean_unsigned_to_nat(4u);
v_structId_960_ = l_Lean_Syntax_getArg(v_x_918_, v___x_959_);
lean_inc(v_structId_960_);
v___x_961_ = l_Lean_Syntax_isOfKind(v_structId_960_, v___x_955_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec(v_structId_960_);
lean_dec(v_elabId_954_);
lean_dec(v_visibility_x3f_950_);
lean_dec(v___y_949_);
lean_dec(v_x_918_);
v___x_962_ = l_Lean_Fmt_Error_partialFormatter;
v___x_963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___y_952_);
return v___x_963_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; size_t v_sz_967_; size_t v___x_968_; lean_object* v___x_969_; 
v___x_964_ = lean_unsigned_to_nat(5u);
v___x_965_ = l_Lean_Syntax_getArg(v_x_918_, v___x_964_);
v___x_966_ = l_Lean_Syntax_getArgs(v___x_965_);
lean_dec(v___x_965_);
v_sz_967_ = lean_array_size(v___x_966_);
v___x_968_ = ((size_t)0ULL);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDefEvalConfigItemCmd_spec__0(v_sz_967_, v___x_968_, v___x_966_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec(v_structId_960_);
lean_dec(v_elabId_954_);
lean_dec(v_visibility_x3f_950_);
lean_dec(v___y_949_);
lean_dec(v_x_918_);
v___x_970_ = l_Lean_Fmt_Error_partialFormatter;
v___x_971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v___y_952_);
return v___x_971_;
}
else
{
lean_object* v_val_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_993_; 
v_val_972_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_993_ == 0)
{
v___x_974_ = v___x_969_;
v_isShared_975_ = v_isSharedCheck_993_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_val_972_);
lean_dec(v___x_969_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_993_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v_declTk_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_976_ = lean_unsigned_to_nat(2u);
v_declTk_977_ = l_Lean_Syntax_getArg(v_x_918_, v___x_976_);
v___x_978_ = lean_unsigned_to_nat(6u);
v___x_979_ = l_Lean_Syntax_getArg(v_x_918_, v___x_978_);
lean_dec(v_x_918_);
v___x_980_ = l_Lean_Syntax_isNone(v___x_979_);
if (v___x_980_ == 0)
{
uint8_t v___x_981_; 
lean_inc(v___x_979_);
v___x_981_ = l_Lean_Syntax_matchesNull(v___x_979_, v___y_948_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec(v___x_979_);
lean_dec(v_declTk_977_);
lean_del_object(v___x_974_);
lean_dec(v_val_972_);
lean_dec(v_structId_960_);
lean_dec(v_elabId_954_);
lean_dec(v_visibility_x3f_950_);
lean_dec(v___y_949_);
v___x_982_ = l_Lean_Fmt_Error_partialFormatter;
v___x_983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___y_952_);
return v___x_983_;
}
else
{
lean_object* v_configEntries_x3f_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_configEntries_x3f_984_ = l_Lean_Syntax_getArg(v___x_979_, v___x_946_);
lean_dec(v___x_979_);
v___x_985_ = ((lean_object*)(l_Lean_Fmt_fmtWithConfigEntries___closed__1));
lean_inc(v_configEntries_x3f_984_);
v___x_986_ = l_Lean_Syntax_isOfKind(v_configEntries_x3f_984_, v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec(v_configEntries_x3f_984_);
lean_dec(v_declTk_977_);
lean_del_object(v___x_974_);
lean_dec(v_val_972_);
lean_dec(v_structId_960_);
lean_dec(v_elabId_954_);
lean_dec(v_visibility_x3f_950_);
lean_dec(v___y_949_);
v___x_987_ = l_Lean_Fmt_Error_partialFormatter;
v___x_988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___y_952_);
return v___x_988_;
}
else
{
lean_object* v___x_990_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v_configEntries_x3f_984_);
v___x_990_ = v___x_974_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_configEntries_x3f_984_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
v___y_922_ = v_elabId_954_;
v___y_923_ = v_visibility_x3f_950_;
v___y_924_ = v_declTk_977_;
v___y_925_ = v___y_949_;
v___y_926_ = v_structId_960_;
v___y_927_ = v_val_972_;
v_configEntries_x3f_928_ = v___x_990_;
v___y_929_ = v___y_951_;
v___y_930_ = v___y_952_;
goto v___jp_921_;
}
}
}
}
else
{
lean_object* v___x_992_; 
lean_dec(v___x_979_);
lean_del_object(v___x_974_);
v___x_992_ = lean_box(0);
v___y_922_ = v_elabId_954_;
v___y_923_ = v_visibility_x3f_950_;
v___y_924_ = v_declTk_977_;
v___y_925_ = v___y_949_;
v___y_926_ = v_structId_960_;
v___y_927_ = v_val_972_;
v_configEntries_x3f_928_ = v___x_992_;
v___y_929_ = v___y_951_;
v___y_930_ = v___y_952_;
goto v___jp_921_;
}
}
}
}
}
}
v___jp_994_:
{
lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_998_ = lean_unsigned_to_nat(1u);
v___x_999_ = l_Lean_Syntax_getArg(v_x_918_, v___x_998_);
v___x_1000_ = l_Lean_Syntax_isNone(v___x_999_);
if (v___x_1000_ == 0)
{
uint8_t v___x_1001_; 
lean_inc(v___x_999_);
v___x_1001_ = l_Lean_Syntax_matchesNull(v___x_999_, v___x_998_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec(v___x_999_);
lean_dec(v_docComment_x3f_995_);
lean_dec(v_x_918_);
v___x_1002_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___y_997_);
return v___x_1003_;
}
else
{
lean_object* v_visibility_x3f_1004_; lean_object* v___x_1005_; 
v_visibility_x3f_1004_ = l_Lean_Syntax_getArg(v___x_999_, v___x_946_);
lean_dec(v___x_999_);
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_visibility_x3f_1004_);
v___y_948_ = v___x_998_;
v___y_949_ = v_docComment_x3f_995_;
v_visibility_x3f_950_ = v___x_1005_;
v___y_951_ = v___y_996_;
v___y_952_ = v___y_997_;
goto v___jp_947_;
}
}
else
{
lean_object* v___x_1006_; 
lean_dec(v___x_999_);
v___x_1006_ = lean_box(0);
v___y_948_ = v___x_998_;
v___y_949_ = v_docComment_x3f_995_;
v_visibility_x3f_950_ = v___x_1006_;
v___y_951_ = v___y_996_;
v___y_952_ = v___y_997_;
goto v___jp_947_;
}
}
}
v___jp_921_:
{
if (lean_obj_tag(v___y_923_) == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_box(0);
v___x_932_ = l_Lean_Fmt_fmtDeclareConfig(v___y_925_, v___x_931_, v___y_924_, v___y_922_, v___y_926_, v___y_927_, v_configEntries_x3f_928_, v___y_929_, v___y_930_);
return v___x_932_;
}
else
{
lean_object* v_val_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_941_; 
v_val_933_ = lean_ctor_get(v___y_923_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___y_923_);
if (v_isSharedCheck_941_ == 0)
{
v___x_935_ = v___y_923_;
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_val_933_);
lean_dec(v___y_923_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_val_933_);
v___x_938_ = v_reuseFailAlloc_940_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Fmt_fmtDeclareConfig(v___y_925_, v___x_938_, v___y_924_, v___y_922_, v___y_926_, v___y_927_, v_configEntries_x3f_928_, v___y_929_, v___y_930_);
return v___x_939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareCoreConfigElab___boxed(lean_object* v_x_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Fmt_fmtDeclareCoreConfigElab(v_x_1020_, v_a_1021_, v_a_1022_);
lean_dec_ref(v_a_1021_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1(){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1030_ = l_Lean_Fmt_fmtAttribute;
v___x_1031_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareCoreConfigElab___closed__1));
v___x_1032_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___closed__1));
v___x_1033_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDeclareCoreConfigElab___boxed), 3, 0);
v___x_1034_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1030_, v___x_1031_, v___x_1032_, v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1___boxed(lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1();
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareTermConfigElab(lean_object* v_x_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v_configEntries_x3f_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareTermConfigElab___closed__1));
lean_inc(v_x_1043_);
v___x_1068_ = l_Lean_Syntax_isOfKind(v_x_1043_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_dec(v_x_1043_);
v___x_1069_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v_a_1045_);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v_visibility_x3f_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v_docComment_x3f_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1132_ = l_Lean_Syntax_getArg(v_x_1043_, v___x_1071_);
v___x_1133_ = l_Lean_Syntax_isNone(v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1132_);
v___x_1135_ = l_Lean_Syntax_matchesNull(v___x_1132_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec(v___x_1132_);
lean_dec(v_x_1043_);
v___x_1136_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v_a_1045_);
return v___x_1137_;
}
else
{
lean_object* v_docComment_x3f_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v_docComment_x3f_1138_ = l_Lean_Syntax_getArg(v___x_1132_, v___x_1071_);
lean_dec(v___x_1132_);
v___x_1139_ = ((lean_object*)(l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4));
lean_inc(v_docComment_x3f_1138_);
v___x_1140_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_1138_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec(v_docComment_x3f_1138_);
lean_dec(v_x_1043_);
v___x_1141_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v_a_1045_);
return v___x_1142_;
}
else
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1143_, 0, v_docComment_x3f_1138_);
v_docComment_x3f_1120_ = v___x_1143_;
v___y_1121_ = v_a_1044_;
v___y_1122_ = v_a_1045_;
goto v___jp_1119_;
}
}
}
else
{
lean_object* v___x_1144_; 
lean_dec(v___x_1132_);
v___x_1144_ = lean_box(0);
v_docComment_x3f_1120_ = v___x_1144_;
v___y_1121_ = v_a_1044_;
v___y_1122_ = v_a_1045_;
goto v___jp_1119_;
}
v___jp_1072_:
{
lean_object* v___x_1078_; lean_object* v_elabId_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1078_ = lean_unsigned_to_nat(3u);
v_elabId_1079_ = l_Lean_Syntax_getArg(v_x_1043_, v___x_1078_);
v___x_1080_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__3));
lean_inc(v_elabId_1079_);
v___x_1081_ = l_Lean_Syntax_isOfKind(v_elabId_1079_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v_elabId_1079_);
lean_dec(v_visibility_x3f_1075_);
lean_dec(v___y_1073_);
lean_dec(v_x_1043_);
v___x_1082_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v___y_1077_);
return v___x_1083_;
}
else
{
lean_object* v___x_1084_; lean_object* v_structId_1085_; uint8_t v___x_1086_; 
v___x_1084_ = lean_unsigned_to_nat(4u);
v_structId_1085_ = l_Lean_Syntax_getArg(v_x_1043_, v___x_1084_);
lean_inc(v_structId_1085_);
v___x_1086_ = l_Lean_Syntax_isOfKind(v_structId_1085_, v___x_1080_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_dec(v_structId_1085_);
lean_dec(v_elabId_1079_);
lean_dec(v_visibility_x3f_1075_);
lean_dec(v___y_1073_);
lean_dec(v_x_1043_);
v___x_1087_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v___y_1077_);
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; size_t v_sz_1092_; size_t v___x_1093_; lean_object* v___x_1094_; 
v___x_1089_ = lean_unsigned_to_nat(5u);
v___x_1090_ = l_Lean_Syntax_getArg(v_x_1043_, v___x_1089_);
v___x_1091_ = l_Lean_Syntax_getArgs(v___x_1090_);
lean_dec(v___x_1090_);
v_sz_1092_ = lean_array_size(v___x_1091_);
v___x_1093_ = ((size_t)0ULL);
v___x_1094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDefEvalConfigItemCmd_spec__0(v_sz_1092_, v___x_1093_, v___x_1091_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v_structId_1085_);
lean_dec(v_elabId_1079_);
lean_dec(v_visibility_x3f_1075_);
lean_dec(v___y_1073_);
lean_dec(v_x_1043_);
v___x_1095_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v___y_1077_);
return v___x_1096_;
}
else
{
lean_object* v_val_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1118_; 
v_val_1097_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1099_ = v___x_1094_;
v_isShared_1100_ = v_isSharedCheck_1118_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_val_1097_);
lean_dec(v___x_1094_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1118_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v_declTk_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1101_ = lean_unsigned_to_nat(2u);
v_declTk_1102_ = l_Lean_Syntax_getArg(v_x_1043_, v___x_1101_);
v___x_1103_ = lean_unsigned_to_nat(6u);
v___x_1104_ = l_Lean_Syntax_getArg(v_x_1043_, v___x_1103_);
lean_dec(v_x_1043_);
v___x_1105_ = l_Lean_Syntax_isNone(v___x_1104_);
if (v___x_1105_ == 0)
{
uint8_t v___x_1106_; 
lean_inc(v___x_1104_);
v___x_1106_ = l_Lean_Syntax_matchesNull(v___x_1104_, v___y_1074_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec(v___x_1104_);
lean_dec(v_declTk_1102_);
lean_del_object(v___x_1099_);
lean_dec(v_val_1097_);
lean_dec(v_structId_1085_);
lean_dec(v_elabId_1079_);
lean_dec(v_visibility_x3f_1075_);
lean_dec(v___y_1073_);
v___x_1107_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v___y_1077_);
return v___x_1108_;
}
else
{
lean_object* v_configEntries_x3f_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_configEntries_x3f_1109_ = l_Lean_Syntax_getArg(v___x_1104_, v___x_1071_);
lean_dec(v___x_1104_);
v___x_1110_ = ((lean_object*)(l_Lean_Fmt_fmtWithConfigEntries___closed__1));
lean_inc(v_configEntries_x3f_1109_);
v___x_1111_ = l_Lean_Syntax_isOfKind(v_configEntries_x3f_1109_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_dec(v_configEntries_x3f_1109_);
lean_dec(v_declTk_1102_);
lean_del_object(v___x_1099_);
lean_dec(v_val_1097_);
lean_dec(v_structId_1085_);
lean_dec(v_elabId_1079_);
lean_dec(v_visibility_x3f_1075_);
lean_dec(v___y_1073_);
v___x_1112_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v___y_1077_);
return v___x_1113_;
}
else
{
lean_object* v___x_1115_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v_configEntries_x3f_1109_);
v___x_1115_ = v___x_1099_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_configEntries_x3f_1109_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
v___y_1047_ = v_structId_1085_;
v___y_1048_ = v_declTk_1102_;
v___y_1049_ = v___y_1073_;
v___y_1050_ = v_val_1097_;
v___y_1051_ = v_elabId_1079_;
v___y_1052_ = v_visibility_x3f_1075_;
v_configEntries_x3f_1053_ = v___x_1115_;
v___y_1054_ = v___y_1076_;
v___y_1055_ = v___y_1077_;
goto v___jp_1046_;
}
}
}
}
else
{
lean_object* v___x_1117_; 
lean_dec(v___x_1104_);
lean_del_object(v___x_1099_);
v___x_1117_ = lean_box(0);
v___y_1047_ = v_structId_1085_;
v___y_1048_ = v_declTk_1102_;
v___y_1049_ = v___y_1073_;
v___y_1050_ = v_val_1097_;
v___y_1051_ = v_elabId_1079_;
v___y_1052_ = v_visibility_x3f_1075_;
v_configEntries_x3f_1053_ = v___x_1117_;
v___y_1054_ = v___y_1076_;
v___y_1055_ = v___y_1077_;
goto v___jp_1046_;
}
}
}
}
}
}
v___jp_1119_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1123_ = lean_unsigned_to_nat(1u);
v___x_1124_ = l_Lean_Syntax_getArg(v_x_1043_, v___x_1123_);
v___x_1125_ = l_Lean_Syntax_isNone(v___x_1124_);
if (v___x_1125_ == 0)
{
uint8_t v___x_1126_; 
lean_inc(v___x_1124_);
v___x_1126_ = l_Lean_Syntax_matchesNull(v___x_1124_, v___x_1123_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_dec(v___x_1124_);
lean_dec(v_docComment_x3f_1120_);
lean_dec(v_x_1043_);
v___x_1127_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v___y_1122_);
return v___x_1128_;
}
else
{
lean_object* v_visibility_x3f_1129_; lean_object* v___x_1130_; 
v_visibility_x3f_1129_ = l_Lean_Syntax_getArg(v___x_1124_, v___x_1071_);
lean_dec(v___x_1124_);
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_visibility_x3f_1129_);
v___y_1073_ = v_docComment_x3f_1120_;
v___y_1074_ = v___x_1123_;
v_visibility_x3f_1075_ = v___x_1130_;
v___y_1076_ = v___y_1121_;
v___y_1077_ = v___y_1122_;
goto v___jp_1072_;
}
}
else
{
lean_object* v___x_1131_; 
lean_dec(v___x_1124_);
v___x_1131_ = lean_box(0);
v___y_1073_ = v_docComment_x3f_1120_;
v___y_1074_ = v___x_1123_;
v_visibility_x3f_1075_ = v___x_1131_;
v___y_1076_ = v___y_1121_;
v___y_1077_ = v___y_1122_;
goto v___jp_1072_;
}
}
}
v___jp_1046_:
{
if (lean_obj_tag(v___y_1052_) == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_box(0);
v___x_1057_ = l_Lean_Fmt_fmtDeclareConfig(v___y_1049_, v___x_1056_, v___y_1048_, v___y_1051_, v___y_1047_, v___y_1050_, v_configEntries_x3f_1053_, v___y_1054_, v___y_1055_);
return v___x_1057_;
}
else
{
lean_object* v_val_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1066_; 
v_val_1058_ = lean_ctor_get(v___y_1052_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___y_1052_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1060_ = v___y_1052_;
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_val_1058_);
lean_dec(v___y_1052_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_val_1058_);
v___x_1063_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_Fmt_fmtDeclareConfig(v___y_1049_, v___x_1063_, v___y_1048_, v___y_1051_, v___y_1047_, v___y_1050_, v_configEntries_x3f_1053_, v___y_1054_, v___y_1055_);
return v___x_1064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareTermConfigElab___boxed(lean_object* v_x_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Fmt_fmtDeclareTermConfigElab(v_x_1145_, v_a_1146_, v_a_1147_);
lean_dec_ref(v_a_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1(){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1155_ = l_Lean_Fmt_fmtAttribute;
v___x_1156_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareTermConfigElab___closed__1));
v___x_1157_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___closed__1));
v___x_1158_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDeclareTermConfigElab___boxed), 3, 0);
v___x_1159_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1155_, v___x_1156_, v___x_1157_, v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1___boxed(lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1();
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareTacticConfig(lean_object* v_x_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v_configEntries_x3f_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareTacticConfig___closed__1));
lean_inc(v_x_1168_);
v___x_1193_ = l_Lean_Syntax_isOfKind(v_x_1168_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec(v_x_1168_);
v___x_1194_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v_a_1170_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v_visibility_x3f_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v_docComment_x3f_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1257_ = l_Lean_Syntax_getArg(v_x_1168_, v___x_1196_);
v___x_1258_ = l_Lean_Syntax_isNone(v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1257_);
v___x_1260_ = l_Lean_Syntax_matchesNull(v___x_1257_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec(v___x_1257_);
lean_dec(v_x_1168_);
v___x_1261_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v_a_1170_);
return v___x_1262_;
}
else
{
lean_object* v_docComment_x3f_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_docComment_x3f_1263_ = l_Lean_Syntax_getArg(v___x_1257_, v___x_1196_);
lean_dec(v___x_1257_);
v___x_1264_ = ((lean_object*)(l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4));
lean_inc(v_docComment_x3f_1263_);
v___x_1265_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec(v_docComment_x3f_1263_);
lean_dec(v_x_1168_);
v___x_1266_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v_a_1170_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1268_, 0, v_docComment_x3f_1263_);
v_docComment_x3f_1245_ = v___x_1268_;
v___y_1246_ = v_a_1169_;
v___y_1247_ = v_a_1170_;
goto v___jp_1244_;
}
}
}
else
{
lean_object* v___x_1269_; 
lean_dec(v___x_1257_);
v___x_1269_ = lean_box(0);
v_docComment_x3f_1245_ = v___x_1269_;
v___y_1246_ = v_a_1169_;
v___y_1247_ = v_a_1170_;
goto v___jp_1244_;
}
v___jp_1197_:
{
lean_object* v___x_1203_; lean_object* v_elabId_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1203_ = lean_unsigned_to_nat(3u);
v_elabId_1204_ = l_Lean_Syntax_getArg(v_x_1168_, v___x_1203_);
v___x_1205_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__3));
lean_inc(v_elabId_1204_);
v___x_1206_ = l_Lean_Syntax_isOfKind(v_elabId_1204_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_dec(v_elabId_1204_);
lean_dec(v_visibility_x3f_1200_);
lean_dec(v___y_1199_);
lean_dec(v_x_1168_);
v___x_1207_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___y_1202_);
return v___x_1208_;
}
else
{
lean_object* v___x_1209_; lean_object* v_structId_1210_; uint8_t v___x_1211_; 
v___x_1209_ = lean_unsigned_to_nat(4u);
v_structId_1210_ = l_Lean_Syntax_getArg(v_x_1168_, v___x_1209_);
lean_inc(v_structId_1210_);
v___x_1211_ = l_Lean_Syntax_isOfKind(v_structId_1210_, v___x_1205_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_dec(v_structId_1210_);
lean_dec(v_elabId_1204_);
lean_dec(v_visibility_x3f_1200_);
lean_dec(v___y_1199_);
lean_dec(v_x_1168_);
v___x_1212_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___y_1202_);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; size_t v_sz_1217_; size_t v___x_1218_; lean_object* v___x_1219_; 
v___x_1214_ = lean_unsigned_to_nat(5u);
v___x_1215_ = l_Lean_Syntax_getArg(v_x_1168_, v___x_1214_);
v___x_1216_ = l_Lean_Syntax_getArgs(v___x_1215_);
lean_dec(v___x_1215_);
v_sz_1217_ = lean_array_size(v___x_1216_);
v___x_1218_ = ((size_t)0ULL);
v___x_1219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDefEvalConfigItemCmd_spec__0(v_sz_1217_, v___x_1218_, v___x_1216_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec(v_structId_1210_);
lean_dec(v_elabId_1204_);
lean_dec(v_visibility_x3f_1200_);
lean_dec(v___y_1199_);
lean_dec(v_x_1168_);
v___x_1220_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___y_1202_);
return v___x_1221_;
}
else
{
lean_object* v_val_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1243_; 
v_val_1222_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1224_ = v___x_1219_;
v_isShared_1225_ = v_isSharedCheck_1243_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_val_1222_);
lean_dec(v___x_1219_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1243_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v_declTk_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1226_ = lean_unsigned_to_nat(2u);
v_declTk_1227_ = l_Lean_Syntax_getArg(v_x_1168_, v___x_1226_);
v___x_1228_ = lean_unsigned_to_nat(6u);
v___x_1229_ = l_Lean_Syntax_getArg(v_x_1168_, v___x_1228_);
lean_dec(v_x_1168_);
v___x_1230_ = l_Lean_Syntax_isNone(v___x_1229_);
if (v___x_1230_ == 0)
{
uint8_t v___x_1231_; 
lean_inc(v___x_1229_);
v___x_1231_ = l_Lean_Syntax_matchesNull(v___x_1229_, v___y_1198_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec(v___x_1229_);
lean_dec(v_declTk_1227_);
lean_del_object(v___x_1224_);
lean_dec(v_val_1222_);
lean_dec(v_structId_1210_);
lean_dec(v_elabId_1204_);
lean_dec(v_visibility_x3f_1200_);
lean_dec(v___y_1199_);
v___x_1232_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v___y_1202_);
return v___x_1233_;
}
else
{
lean_object* v_configEntries_x3f_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v_configEntries_x3f_1234_ = l_Lean_Syntax_getArg(v___x_1229_, v___x_1196_);
lean_dec(v___x_1229_);
v___x_1235_ = ((lean_object*)(l_Lean_Fmt_fmtWithConfigEntries___closed__1));
lean_inc(v_configEntries_x3f_1234_);
v___x_1236_ = l_Lean_Syntax_isOfKind(v_configEntries_x3f_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v_configEntries_x3f_1234_);
lean_dec(v_declTk_1227_);
lean_del_object(v___x_1224_);
lean_dec(v_val_1222_);
lean_dec(v_structId_1210_);
lean_dec(v_elabId_1204_);
lean_dec(v_visibility_x3f_1200_);
lean_dec(v___y_1199_);
v___x_1237_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v___y_1202_);
return v___x_1238_;
}
else
{
lean_object* v___x_1240_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v_configEntries_x3f_1234_);
v___x_1240_ = v___x_1224_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_configEntries_x3f_1234_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
v___y_1172_ = v_val_1222_;
v___y_1173_ = v_declTk_1227_;
v___y_1174_ = v_elabId_1204_;
v___y_1175_ = v___y_1199_;
v___y_1176_ = v_structId_1210_;
v___y_1177_ = v_visibility_x3f_1200_;
v_configEntries_x3f_1178_ = v___x_1240_;
v___y_1179_ = v___y_1201_;
v___y_1180_ = v___y_1202_;
goto v___jp_1171_;
}
}
}
}
else
{
lean_object* v___x_1242_; 
lean_dec(v___x_1229_);
lean_del_object(v___x_1224_);
v___x_1242_ = lean_box(0);
v___y_1172_ = v_val_1222_;
v___y_1173_ = v_declTk_1227_;
v___y_1174_ = v_elabId_1204_;
v___y_1175_ = v___y_1199_;
v___y_1176_ = v_structId_1210_;
v___y_1177_ = v_visibility_x3f_1200_;
v_configEntries_x3f_1178_ = v___x_1242_;
v___y_1179_ = v___y_1201_;
v___y_1180_ = v___y_1202_;
goto v___jp_1171_;
}
}
}
}
}
}
v___jp_1244_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1248_ = lean_unsigned_to_nat(1u);
v___x_1249_ = l_Lean_Syntax_getArg(v_x_1168_, v___x_1248_);
v___x_1250_ = l_Lean_Syntax_isNone(v___x_1249_);
if (v___x_1250_ == 0)
{
uint8_t v___x_1251_; 
lean_inc(v___x_1249_);
v___x_1251_ = l_Lean_Syntax_matchesNull(v___x_1249_, v___x_1248_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec(v___x_1249_);
lean_dec(v_docComment_x3f_1245_);
lean_dec(v_x_1168_);
v___x_1252_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v___y_1247_);
return v___x_1253_;
}
else
{
lean_object* v_visibility_x3f_1254_; lean_object* v___x_1255_; 
v_visibility_x3f_1254_ = l_Lean_Syntax_getArg(v___x_1249_, v___x_1196_);
lean_dec(v___x_1249_);
v___x_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_visibility_x3f_1254_);
v___y_1198_ = v___x_1248_;
v___y_1199_ = v_docComment_x3f_1245_;
v_visibility_x3f_1200_ = v___x_1255_;
v___y_1201_ = v___y_1246_;
v___y_1202_ = v___y_1247_;
goto v___jp_1197_;
}
}
else
{
lean_object* v___x_1256_; 
lean_dec(v___x_1249_);
v___x_1256_ = lean_box(0);
v___y_1198_ = v___x_1248_;
v___y_1199_ = v_docComment_x3f_1245_;
v_visibility_x3f_1200_ = v___x_1256_;
v___y_1201_ = v___y_1246_;
v___y_1202_ = v___y_1247_;
goto v___jp_1197_;
}
}
}
v___jp_1171_:
{
if (lean_obj_tag(v___y_1177_) == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_box(0);
v___x_1182_ = l_Lean_Fmt_fmtDeclareConfig(v___y_1175_, v___x_1181_, v___y_1173_, v___y_1174_, v___y_1176_, v___y_1172_, v_configEntries_x3f_1178_, v___y_1179_, v___y_1180_);
return v___x_1182_;
}
else
{
lean_object* v_val_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1191_; 
v_val_1183_ = lean_ctor_get(v___y_1177_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___y_1177_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1185_ = v___y_1177_;
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_val_1183_);
lean_dec(v___y_1177_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_val_1183_);
v___x_1188_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Fmt_fmtDeclareConfig(v___y_1175_, v___x_1188_, v___y_1173_, v___y_1174_, v___y_1176_, v___y_1172_, v_configEntries_x3f_1178_, v___y_1179_, v___y_1180_);
return v___x_1189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareTacticConfig___boxed(lean_object* v_x_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Fmt_fmtDeclareTacticConfig(v_x_1270_, v_a_1271_, v_a_1272_);
lean_dec_ref(v_a_1271_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1(){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1280_ = l_Lean_Fmt_fmtAttribute;
v___x_1281_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareTacticConfig___closed__1));
v___x_1282_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___closed__1));
v___x_1283_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDeclareTacticConfig___boxed), 3, 0);
v___x_1284_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1280_, v___x_1281_, v___x_1282_, v___x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1___boxed(lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1();
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareCommandConfig(lean_object* v_x_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v_configEntries_x3f_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareCommandConfig___closed__1));
lean_inc(v_x_1293_);
v___x_1318_ = l_Lean_Syntax_isOfKind(v_x_1293_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_dec(v_x_1293_);
v___x_1319_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v_a_1295_);
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v_visibility_x3f_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v_docComment_x3f_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1321_ = lean_unsigned_to_nat(0u);
v___x_1382_ = l_Lean_Syntax_getArg(v_x_1293_, v___x_1321_);
v___x_1383_ = l_Lean_Syntax_isNone(v___x_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1384_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1382_);
v___x_1385_ = l_Lean_Syntax_matchesNull(v___x_1382_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec(v___x_1382_);
lean_dec(v_x_1293_);
v___x_1386_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v_a_1295_);
return v___x_1387_;
}
else
{
lean_object* v_docComment_x3f_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v_docComment_x3f_1388_ = l_Lean_Syntax_getArg(v___x_1382_, v___x_1321_);
lean_dec(v___x_1382_);
v___x_1389_ = ((lean_object*)(l_Lean_Fmt_fmtDefEvalConfigItemCmd___closed__4));
lean_inc(v_docComment_x3f_1388_);
v___x_1390_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_1388_, v___x_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec(v_docComment_x3f_1388_);
lean_dec(v_x_1293_);
v___x_1391_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
lean_ctor_set(v___x_1392_, 1, v_a_1295_);
return v___x_1392_;
}
else
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_docComment_x3f_1388_);
v_docComment_x3f_1370_ = v___x_1393_;
v___y_1371_ = v_a_1294_;
v___y_1372_ = v_a_1295_;
goto v___jp_1369_;
}
}
}
else
{
lean_object* v___x_1394_; 
lean_dec(v___x_1382_);
v___x_1394_ = lean_box(0);
v_docComment_x3f_1370_ = v___x_1394_;
v___y_1371_ = v_a_1294_;
v___y_1372_ = v_a_1295_;
goto v___jp_1369_;
}
v___jp_1322_:
{
lean_object* v___x_1328_; lean_object* v_elabId_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1328_ = lean_unsigned_to_nat(3u);
v_elabId_1329_ = l_Lean_Syntax_getArg(v_x_1293_, v___x_1328_);
v___x_1330_ = ((lean_object*)(l_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___closed__3));
lean_inc(v_elabId_1329_);
v___x_1331_ = l_Lean_Syntax_isOfKind(v_elabId_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec(v_elabId_1329_);
lean_dec(v_visibility_x3f_1325_);
lean_dec(v___y_1324_);
lean_dec(v_x_1293_);
v___x_1332_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v___y_1327_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; lean_object* v_structId_1335_; uint8_t v___x_1336_; 
v___x_1334_ = lean_unsigned_to_nat(4u);
v_structId_1335_ = l_Lean_Syntax_getArg(v_x_1293_, v___x_1334_);
lean_inc(v_structId_1335_);
v___x_1336_ = l_Lean_Syntax_isOfKind(v_structId_1335_, v___x_1330_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_dec(v_structId_1335_);
lean_dec(v_elabId_1329_);
lean_dec(v_visibility_x3f_1325_);
lean_dec(v___y_1324_);
lean_dec(v_x_1293_);
v___x_1337_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v___y_1327_);
return v___x_1338_;
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; size_t v_sz_1342_; size_t v___x_1343_; lean_object* v___x_1344_; 
v___x_1339_ = lean_unsigned_to_nat(5u);
v___x_1340_ = l_Lean_Syntax_getArg(v_x_1293_, v___x_1339_);
v___x_1341_ = l_Lean_Syntax_getArgs(v___x_1340_);
lean_dec(v___x_1340_);
v_sz_1342_ = lean_array_size(v___x_1341_);
v___x_1343_ = ((size_t)0ULL);
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDefEvalConfigItemCmd_spec__0(v_sz_1342_, v___x_1343_, v___x_1341_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec(v_structId_1335_);
lean_dec(v_elabId_1329_);
lean_dec(v_visibility_x3f_1325_);
lean_dec(v___y_1324_);
lean_dec(v_x_1293_);
v___x_1345_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v___y_1327_);
return v___x_1346_;
}
else
{
lean_object* v_val_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1368_; 
v_val_1347_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1349_ = v___x_1344_;
v_isShared_1350_ = v_isSharedCheck_1368_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_val_1347_);
lean_dec(v___x_1344_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1368_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v_declTk_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1351_ = lean_unsigned_to_nat(2u);
v_declTk_1352_ = l_Lean_Syntax_getArg(v_x_1293_, v___x_1351_);
v___x_1353_ = lean_unsigned_to_nat(6u);
v___x_1354_ = l_Lean_Syntax_getArg(v_x_1293_, v___x_1353_);
lean_dec(v_x_1293_);
v___x_1355_ = l_Lean_Syntax_isNone(v___x_1354_);
if (v___x_1355_ == 0)
{
uint8_t v___x_1356_; 
lean_inc(v___x_1354_);
v___x_1356_ = l_Lean_Syntax_matchesNull(v___x_1354_, v___y_1323_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v___x_1354_);
lean_dec(v_declTk_1352_);
lean_del_object(v___x_1349_);
lean_dec(v_val_1347_);
lean_dec(v_structId_1335_);
lean_dec(v_elabId_1329_);
lean_dec(v_visibility_x3f_1325_);
lean_dec(v___y_1324_);
v___x_1357_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___y_1327_);
return v___x_1358_;
}
else
{
lean_object* v_configEntries_x3f_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v_configEntries_x3f_1359_ = l_Lean_Syntax_getArg(v___x_1354_, v___x_1321_);
lean_dec(v___x_1354_);
v___x_1360_ = ((lean_object*)(l_Lean_Fmt_fmtWithConfigEntries___closed__1));
lean_inc(v_configEntries_x3f_1359_);
v___x_1361_ = l_Lean_Syntax_isOfKind(v_configEntries_x3f_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec(v_configEntries_x3f_1359_);
lean_dec(v_declTk_1352_);
lean_del_object(v___x_1349_);
lean_dec(v_val_1347_);
lean_dec(v_structId_1335_);
lean_dec(v_elabId_1329_);
lean_dec(v_visibility_x3f_1325_);
lean_dec(v___y_1324_);
v___x_1362_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
lean_ctor_set(v___x_1363_, 1, v___y_1327_);
return v___x_1363_;
}
else
{
lean_object* v___x_1365_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v_configEntries_x3f_1359_);
v___x_1365_ = v___x_1349_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_configEntries_x3f_1359_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
v___y_1297_ = v___y_1324_;
v___y_1298_ = v_elabId_1329_;
v___y_1299_ = v_structId_1335_;
v___y_1300_ = v_visibility_x3f_1325_;
v___y_1301_ = v_declTk_1352_;
v___y_1302_ = v_val_1347_;
v_configEntries_x3f_1303_ = v___x_1365_;
v___y_1304_ = v___y_1326_;
v___y_1305_ = v___y_1327_;
goto v___jp_1296_;
}
}
}
}
else
{
lean_object* v___x_1367_; 
lean_dec(v___x_1354_);
lean_del_object(v___x_1349_);
v___x_1367_ = lean_box(0);
v___y_1297_ = v___y_1324_;
v___y_1298_ = v_elabId_1329_;
v___y_1299_ = v_structId_1335_;
v___y_1300_ = v_visibility_x3f_1325_;
v___y_1301_ = v_declTk_1352_;
v___y_1302_ = v_val_1347_;
v_configEntries_x3f_1303_ = v___x_1367_;
v___y_1304_ = v___y_1326_;
v___y_1305_ = v___y_1327_;
goto v___jp_1296_;
}
}
}
}
}
}
v___jp_1369_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = l_Lean_Syntax_getArg(v_x_1293_, v___x_1373_);
v___x_1375_ = l_Lean_Syntax_isNone(v___x_1374_);
if (v___x_1375_ == 0)
{
uint8_t v___x_1376_; 
lean_inc(v___x_1374_);
v___x_1376_ = l_Lean_Syntax_matchesNull(v___x_1374_, v___x_1373_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec(v___x_1374_);
lean_dec(v_docComment_x3f_1370_);
lean_dec(v_x_1293_);
v___x_1377_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v___y_1372_);
return v___x_1378_;
}
else
{
lean_object* v_visibility_x3f_1379_; lean_object* v___x_1380_; 
v_visibility_x3f_1379_ = l_Lean_Syntax_getArg(v___x_1374_, v___x_1321_);
lean_dec(v___x_1374_);
v___x_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1380_, 0, v_visibility_x3f_1379_);
v___y_1323_ = v___x_1373_;
v___y_1324_ = v_docComment_x3f_1370_;
v_visibility_x3f_1325_ = v___x_1380_;
v___y_1326_ = v___y_1371_;
v___y_1327_ = v___y_1372_;
goto v___jp_1322_;
}
}
else
{
lean_object* v___x_1381_; 
lean_dec(v___x_1374_);
v___x_1381_ = lean_box(0);
v___y_1323_ = v___x_1373_;
v___y_1324_ = v_docComment_x3f_1370_;
v_visibility_x3f_1325_ = v___x_1381_;
v___y_1326_ = v___y_1371_;
v___y_1327_ = v___y_1372_;
goto v___jp_1322_;
}
}
}
v___jp_1296_:
{
if (lean_obj_tag(v___y_1300_) == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = l_Lean_Fmt_fmtDeclareConfig(v___y_1297_, v___x_1306_, v___y_1301_, v___y_1298_, v___y_1299_, v___y_1302_, v_configEntries_x3f_1303_, v___y_1304_, v___y_1305_);
return v___x_1307_;
}
else
{
lean_object* v_val_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1316_; 
v_val_1308_ = lean_ctor_get(v___y_1300_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___y_1300_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1310_ = v___y_1300_;
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_val_1308_);
lean_dec(v___y_1300_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_val_1308_);
v___x_1313_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Fmt_fmtDeclareConfig(v___y_1297_, v___x_1313_, v___y_1301_, v___y_1298_, v___y_1299_, v___y_1302_, v_configEntries_x3f_1303_, v___y_1304_, v___y_1305_);
return v___x_1314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareCommandConfig___boxed(lean_object* v_x_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Fmt_fmtDeclareCommandConfig(v_x_1395_, v_a_1396_, v_a_1397_);
lean_dec_ref(v_a_1396_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1(){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1405_ = l_Lean_Fmt_fmtAttribute;
v___x_1406_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareCommandConfig___closed__1));
v___x_1407_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___closed__1));
v___x_1408_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDeclareCommandConfig___boxed), 3, 0);
v___x_1409_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1405_, v___x_1406_, v___x_1407_, v___x_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1___boxed(lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1();
return v_res_1411_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalTermInstance__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalExprInstance___regBuiltin_Lean_Fmt_fmtEnsureEvalExprInstance__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtEnsureEvalTermExprInstances___regBuiltin_Lean_Fmt_fmtEnsureEvalTermExprInstances__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeriveEvalExprUsingMeta___regBuiltin_Lean_Fmt_fmtDeriveEvalExprUsingMeta__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryOmit___regBuiltin_Lean_Fmt_fmtConfigEntryOmit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKeyPrefix___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKeyPrefix__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandlerKey___regBuiltin_Lean_Fmt_fmtConfigEntryHandlerKey__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntryHandler___regBuiltin_Lean_Fmt_fmtConfigEntryHandler__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtConfigEntry___regBuiltin_Lean_Fmt_fmtConfigEntry__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDefEvalConfigItemCmd___regBuiltin_Lean_Fmt_fmtDefEvalConfigItemCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCoreConfigElab___regBuiltin_Lean_Fmt_fmtDeclareCoreConfigElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTermConfigElab___regBuiltin_Lean_Fmt_fmtDeclareTermConfigElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareTacticConfig___regBuiltin_Lean_Fmt_fmtDeclareTacticConfig__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands_0__Lean_Fmt_fmtDeclareCommandConfig___regBuiltin_Lean_Fmt_fmtDeclareCommandConfig__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Commands(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Elab_ConfigEval_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval_Commands(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Elab_ConfigEval_Commands(builtin);
}
#ifdef __cplusplus
}
#endif
