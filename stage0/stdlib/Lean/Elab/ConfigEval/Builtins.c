// Lean compiler output
// Module: Lean.Elab.ConfigEval.Builtins
// Imports: public import Lean.Elab.ConfigEval.Commands public import Lean.Elab.ConfigEval.DeriveEvalConfigItem import Lean.Linter.MissingDocs
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_MissingDocs_addBuiltinHandler(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*, uint8_t);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_ConfigEval_defEvalConfigItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ensureEvalTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ensureEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ConfigEval"};
static const lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ensureEvalTermInstance"};
static const lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__7_value),LEAN_SCALAR_PTR_LITERAL(188, 241, 114, 217, 47, 253, 4, 219)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "elabEnsureEvalTermInstance"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 194, 196, 169, 20, 95, 98, 52)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ensureEvalExprInstance"};
static const lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 108, 175, 10, 248, 93, 94, 3)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "elabEnsureEvalExprInstance"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 24, 116, 13, 80, 232, 32, 92)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "ensureEvalTermExprInstances"};
static const lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 66, 158, 168, 204, 221, 79, 184)}};
static const lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ensure_eval_term_instance"};
static const lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__2_value;
static const lean_string_object l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ensure_eval_expr_instance"};
static const lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__3_value;
static const lean_string_object l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6;
static const lean_array_object l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "expandEnsureEvalTermExprInstance"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 5, 152, 25, 120, 11, 48, 44)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "deriveEvalExprUsingMeta"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 116, 75, 98, 130, 21, 177, 80)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "elabDeriveEvalExprUsingMeta"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 91, 14, 102, 74, 139, 51, 157)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "configEntry"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 149, 160, 204, 146, 200, 218, 133)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "configEntryOmit"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 140, 111, 202, 251, 168, 170, 75)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "configEntryHandler"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(78, 145, 34, 65, 77, 53, 67, 42)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "configEntryHandlerKey"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(25, 190, 73, 235, 170, 184, 39, 210)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "configEntryHandlerKeyPrefix"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(165, 45, 37, 228, 14, 221, 193, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "configEntryHandlerKeyWildcard"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(81, 192, 13, 21, 20, 44, 232, 93)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0_value)}};
static const lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "configEntries"};
static const lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 127, 108, 166, 156, 181, 170, 30)}};
static const lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "defEvalConfigItemCmd"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 50, 201, 157, 117, 233, 235, 218)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "elabDefEvalConfigItemCmd"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 139, 45, 169, 210, 187, 151, 127)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "config elab"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__2 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "strictImplicitBinder"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__4 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__4_value),LEAN_SCALAR_PTR_LITERAL(125, 223, 215, 186, 222, 17, 242, 189)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__6 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__6_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unsupported binder"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.Syntax"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__8 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__8_value),LEAN_SCALAR_PTR_LITERAL(45, 144, 98, 72, 115, 31, 20, 74)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9_value)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "binderDefault"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__11 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__11_value),LEAN_SCALAR_PTR_LITERAL(35, 119, 214, 97, 198, 223, 242, 31)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__13 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__13_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term{}"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__15 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__15_value),LEAN_SCALAR_PTR_LITERAL(44, 141, 217, 101, 193, 131, 35, 71)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__19 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__19_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__21 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__21_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__23 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__23_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__23_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value),LEAN_SCALAR_PTR_LITERAL(155, 20, 163, 238, 100, 115, 187, 44)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__28_value)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__30_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__35_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__37_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__39_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__42_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__44_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__46_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__48_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__50_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "EvalConfigItem.defaultOnErr"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "defaultOnErr"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "cfgType\?"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56_value),LEAN_SCALAR_PTR_LITERAL(58, 117, 29, 104, 229, 209, 250, 101)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mkConst"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59_value),LEAN_SCALAR_PTR_LITERAL(37, 117, 8, 90, 26, 147, 93, 249)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59_value),LEAN_SCALAR_PTR_LITERAL(28, 38, 193, 74, 165, 73, 8, 119)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doubleQuotedName"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__63_value),LEAN_SCALAR_PTR_LITERAL(194, 121, 78, 150, 98, 156, 35, 157)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__68 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__68_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__68_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__69_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "logExceptions"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73_value),LEAN_SCALAR_PTR_LITERAL(118, 86, 185, 206, 146, 131, 198, 232)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cfg"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__76 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__76_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__76_value),LEAN_SCALAR_PTR_LITERAL(193, 249, 49, 54, 148, 135, 57, 21)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__79 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__79_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__79_value),LEAN_SCALAR_PTR_LITERAL(72, 5, 38, 228, 229, 249, 19, 211)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "EvalConfigItem.setConfig'"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "EvalConfigItem"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "setConfig'"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86_value),LEAN_SCALAR_PTR_LITERAL(22, 247, 23, 93, 100, 235, 111, 189)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87_value),LEAN_SCALAR_PTR_LITERAL(64, 183, 169, 121, 35, 91, 151, 47)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86_value),LEAN_SCALAR_PTR_LITERAL(16, 84, 54, 65, 212, 237, 250, 172)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value_aux_3),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__87_value),LEAN_SCALAR_PTR_LITERAL(190, 187, 222, 86, 238, 13, 118, 125)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__89_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__90 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__90_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__90_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eval"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92_value),LEAN_SCALAR_PTR_LITERAL(12, 151, 53, 232, 164, 85, 213, 132)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__95_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "onErr"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98_value),LEAN_SCALAR_PTR_LITERAL(228, 46, 52, 217, 218, 46, 201, 51)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalConfigItem"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__104 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__104_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__104_value),LEAN_SCALAR_PTR_LITERAL(180, 209, 241, 176, 164, 63, 27, 216)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106_value),LEAN_SCALAR_PTR_LITERAL(213, 248, 16, 228, 25, 227, 72, 143)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108_value),LEAN_SCALAR_PTR_LITERAL(136, 104, 45, 91, 146, 14, 86, 4)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "def_eval_config_item"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "for"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__111 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__111_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "declareCoreConfigElab"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 30, 123, 201, 158, 66, 128, 147)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Core"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__4_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "CoreM"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 126, 120, 188, 150, 235, 117, 203)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__5_value),LEAN_SCALAR_PTR_LITERAL(115, 114, 191, 177, 45, 189, 121, 141)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__8_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__8_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "elabDeclareCoreConfigElab"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 169, 247, 122, 199, 9, 42, 189)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_&&_"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 195, 203, 117, 177, 125, 57, 22)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "&&"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__8_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedAction"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "read"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(190, 16, 165, 175, 2, 23, 214, 231)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MonadReader"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__16 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__16_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(11, 173, 117, 41, 17, 79, 142, 168)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(46, 74, 177, 199, 30, 224, 37, 71)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__17 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__17_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__18 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__18_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "errToSorry"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__21 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__21_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(167, 166, 138, 245, 152, 171, 48, 109)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__23 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__23_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "declareTermConfigElab"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 108, 165, 103, 249, 154, 177, 123)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___boxed, .m_arity = 8, .m_num_fixed = 5, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "TermElabM"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__3_value),LEAN_SCALAR_PTR_LITERAL(85, 85, 78, 208, 80, 136, 131, 165)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__6_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "elabDeclareTermConfigElab"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 129, 201, 91, 36, 24, 34, 115)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "recover"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 177, 38, 2, 101, 67, 237, 158)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "declareTacticConfig"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 17, 172, 247, 161, 0, 3, 195)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___boxed, .m_arity = 8, .m_num_fixed = 5, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__3_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TacticM"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__3_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 63, 151, 54, 27, 84, 190, 214)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "elabDeclareTacticConfig"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 103, 219, 85, 28, 93, 217, 46)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Command.liftTermElabM"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "liftTermElabM"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "declareCommandConfig"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 49, 172, 65, 140, 146, 127, 103)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___boxed, .m_arity = 8, .m_num_fixed = 5, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__2_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2_value),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2_value;
static const lean_string_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommandElabM"};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__3_value),LEAN_SCALAR_PTR_LITERAL(8, 183, 159, 6, 104, 246, 8, 218)}};
static const lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "elabDeclareCommandConfig"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 8, 37, 243, 138, 220, 183, 157)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 75, 209, 24, 31, 135, 140, 54)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___boxed(lean_object* v_00_u03b1_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0(v_00_u03b1_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___redArg(lean_object* v_a_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___redArg___boxed(lean_object* v_a_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___redArg(v_a_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1(lean_object* v_00_u03b1_37_, lean_object* v_a_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed(lean_object* v_00_u03b1_47_, lean_object* v_a_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1(v_00_u03b1_47_, v_a_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance(lean_object* v_x_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_vis_x3f_79_; lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8));
lean_inc(v_x_74_);
v___x_106_ = l_Lean_Syntax_isOfKind(v_x_74_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
lean_dec(v_x_74_);
v___x_107_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_107_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = l_Lean_Syntax_getArg(v_x_74_, v___x_108_);
v___x_110_ = l_Lean_Syntax_isNone(v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_109_);
v___x_112_ = l_Lean_Syntax_matchesNull(v___x_109_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; 
lean_dec(v___x_109_);
lean_dec(v_x_74_);
v___x_113_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_113_;
}
else
{
lean_object* v_vis_x3f_114_; lean_object* v___x_115_; 
v_vis_x3f_114_ = l_Lean_Syntax_getArg(v___x_109_, v___x_108_);
lean_dec(v___x_109_);
v___x_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_115_, 0, v_vis_x3f_114_);
v_vis_x3f_79_ = v___x_115_;
v___y_80_ = v_a_75_;
v___y_81_ = v_a_76_;
goto v___jp_78_;
}
}
else
{
lean_object* v___x_116_; 
lean_dec(v___x_109_);
v___x_116_ = lean_box(0);
v_vis_x3f_79_ = v___x_116_;
v___y_80_ = v_a_75_;
v___y_81_ = v_a_76_;
goto v___jp_78_;
}
}
v___jp_78_:
{
lean_object* v___x_82_; lean_object* v_kind_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_82_ = lean_unsigned_to_nat(1u);
v_kind_83_ = l_Lean_Syntax_getArg(v_x_74_, v___x_82_);
v___x_84_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
lean_inc(v_kind_83_);
v___x_85_ = l_Lean_Syntax_isOfKind(v_kind_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; 
lean_dec(v_kind_83_);
lean_dec(v_vis_x3f_79_);
lean_dec(v_x_74_);
v___x_86_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_86_;
}
else
{
lean_object* v___x_87_; lean_object* v_tk_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_87_ = lean_unsigned_to_nat(2u);
v_tk_88_ = l_Lean_Syntax_getArg(v_x_74_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = l_Lean_Syntax_getArg(v_x_74_, v___x_89_);
lean_dec(v_x_74_);
v___x_91_ = lean_box(0);
lean_inc(v___x_90_);
v___x_92_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_92_, 0, v___x_90_);
lean_closure_set(v___x_92_, 1, v___x_91_);
v___x_93_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed), 9, 2);
lean_closure_set(v___x_93_, 0, lean_box(0));
lean_closure_set(v___x_93_, 1, v___x_92_);
v___x_94_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_93_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_96_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_a_95_);
lean_dec_ref_known(v___x_94_, 1);
v___x_96_ = l_Lean_Elab_ConfigEval_ensureEvalTerm(v_vis_x3f_79_, v_kind_83_, v_tk_88_, v___x_90_, v_a_95_, v___y_80_, v___y_81_);
return v___x_96_;
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
lean_dec(v___x_90_);
lean_dec(v_tk_88_);
lean_dec(v_kind_83_);
lean_dec(v_vis_x3f_79_);
v_a_97_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_94_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_94_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___boxed(lean_object* v_x_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance(v_x_117_, v_a_118_, v_a_119_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1(){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_129_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_130_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8));
v___x_131_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1));
v___x_132_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___boxed), 4, 0);
v___x_133_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_129_, v___x_130_, v___x_131_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___boxed(lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1();
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance(lean_object* v_x_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_vis_x3f_147_; lean_object* v___y_148_; lean_object* v___y_149_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1));
lean_inc(v_x_142_);
v___x_174_ = l_Lean_Syntax_isOfKind(v_x_142_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_dec(v_x_142_);
v___x_175_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_175_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = l_Lean_Syntax_getArg(v_x_142_, v___x_176_);
v___x_178_ = l_Lean_Syntax_isNone(v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_177_);
v___x_180_ = l_Lean_Syntax_matchesNull(v___x_177_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
lean_dec(v___x_177_);
lean_dec(v_x_142_);
v___x_181_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_181_;
}
else
{
lean_object* v_vis_x3f_182_; lean_object* v___x_183_; 
v_vis_x3f_182_ = l_Lean_Syntax_getArg(v___x_177_, v___x_176_);
lean_dec(v___x_177_);
v___x_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_183_, 0, v_vis_x3f_182_);
v_vis_x3f_147_ = v___x_183_;
v___y_148_ = v_a_143_;
v___y_149_ = v_a_144_;
goto v___jp_146_;
}
}
else
{
lean_object* v___x_184_; 
lean_dec(v___x_177_);
v___x_184_ = lean_box(0);
v_vis_x3f_147_ = v___x_184_;
v___y_148_ = v_a_143_;
v___y_149_ = v_a_144_;
goto v___jp_146_;
}
}
v___jp_146_:
{
lean_object* v___x_150_; lean_object* v_kind_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_150_ = lean_unsigned_to_nat(1u);
v_kind_151_ = l_Lean_Syntax_getArg(v_x_142_, v___x_150_);
v___x_152_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
lean_inc(v_kind_151_);
v___x_153_ = l_Lean_Syntax_isOfKind(v_kind_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; 
lean_dec(v_kind_151_);
lean_dec(v_vis_x3f_147_);
lean_dec(v_x_142_);
v___x_154_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_154_;
}
else
{
lean_object* v___x_155_; lean_object* v_tk_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_155_ = lean_unsigned_to_nat(2u);
v_tk_156_ = l_Lean_Syntax_getArg(v_x_142_, v___x_155_);
v___x_157_ = lean_unsigned_to_nat(3u);
v___x_158_ = l_Lean_Syntax_getArg(v_x_142_, v___x_157_);
lean_dec(v_x_142_);
v___x_159_ = lean_box(0);
lean_inc(v___x_158_);
v___x_160_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_160_, 0, v___x_158_);
lean_closure_set(v___x_160_, 1, v___x_159_);
v___x_161_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed), 9, 2);
lean_closure_set(v___x_161_, 0, lean_box(0));
lean_closure_set(v___x_161_, 1, v___x_160_);
v___x_162_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_161_, v___y_148_, v___y_149_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_164_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_162_, 1);
v___x_164_ = l_Lean_Elab_ConfigEval_ensureEvalExpr(v_vis_x3f_147_, v_kind_151_, v_tk_156_, v___x_158_, v_a_163_, v___y_148_, v___y_149_);
return v___x_164_;
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec(v___x_158_);
lean_dec(v_tk_156_);
lean_dec(v_kind_151_);
lean_dec(v_vis_x3f_147_);
v_a_165_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_162_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_162_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___boxed(lean_object* v_x_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance(v_x_185_, v_a_186_, v_a_187_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1(){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_197_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_198_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1));
v___x_199_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1));
v___x_200_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___boxed), 4, 0);
v___x_201_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_197_, v___x_198_, v___x_199_, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___boxed(lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1();
return v_res_203_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Array_mkArray0___redArg();
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance(lean_object* v_x_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v___x_221_; uint8_t v___x_222_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v_vis_x3f_246_; lean_object* v___y_247_; lean_object* v___y_248_; 
v___x_221_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1));
lean_inc(v_x_218_);
v___x_222_ = l_Lean_Syntax_isOfKind(v_x_218_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_267_; 
lean_dec(v_x_218_);
v___x_267_ = l_Lean_Macro_throwUnsupported___redArg(v_a_220_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = l_Lean_Syntax_getArg(v_x_218_, v___x_268_);
v___x_270_ = l_Lean_Syntax_isNone(v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_269_);
v___x_272_ = l_Lean_Syntax_matchesNull(v___x_269_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
lean_dec(v___x_269_);
lean_dec(v_x_218_);
v___x_273_ = l_Lean_Macro_throwUnsupported___redArg(v_a_220_);
return v___x_273_;
}
else
{
lean_object* v_vis_x3f_274_; lean_object* v___x_275_; 
v_vis_x3f_274_ = l_Lean_Syntax_getArg(v___x_269_, v___x_268_);
lean_dec(v___x_269_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v_vis_x3f_274_);
v_vis_x3f_246_ = v___x_275_;
v___y_247_ = v_a_219_;
v___y_248_ = v_a_220_;
goto v___jp_245_;
}
}
else
{
lean_object* v___x_276_; 
lean_dec(v___x_269_);
v___x_276_ = lean_box(0);
v_vis_x3f_246_ = v___x_276_;
v___y_247_ = v_a_219_;
v___y_248_ = v_a_220_;
goto v___jp_245_;
}
}
v___jp_223_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
lean_inc_ref(v___y_231_);
v___x_233_ = l_Array_append___redArg(v___y_231_, v___y_232_);
lean_dec_ref(v___y_232_);
lean_inc_n(v___y_229_, 2);
lean_inc_n(v___y_230_, 3);
v___x_234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_234_, 0, v___y_230_);
lean_ctor_set(v___x_234_, 1, v___y_229_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
v___x_235_ = l_Lean_SourceInfo_fromRef(v___y_225_, v___x_222_);
lean_dec(v___y_225_);
v___x_236_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__2));
lean_inc(v___x_235_);
v___x_237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
lean_inc(v___y_228_);
lean_inc(v___y_226_);
lean_inc_ref(v___x_234_);
lean_inc(v___y_227_);
v___x_238_ = l_Lean_Syntax_node4(v___y_230_, v___y_227_, v___x_234_, v___y_226_, v___x_237_, v___y_228_);
v___x_239_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1));
v___x_240_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__3));
v___x_241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_235_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = l_Lean_Syntax_node4(v___y_230_, v___x_239_, v___x_234_, v___y_226_, v___x_241_, v___y_228_);
v___x_243_ = l_Lean_Syntax_node2(v___y_230_, v___y_229_, v___x_238_, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___y_224_);
return v___x_244_;
}
v___jp_245_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = l_Lean_Syntax_getArg(v_x_218_, v___x_249_);
v___x_251_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
lean_inc(v___x_250_);
v___x_252_ = l_Lean_Syntax_isOfKind(v___x_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v___x_250_);
lean_dec(v_vis_x3f_246_);
lean_dec(v_x_218_);
v___x_253_ = l_Lean_Macro_throwUnsupported___redArg(v___y_248_);
return v___x_253_;
}
else
{
lean_object* v_ref_254_; lean_object* v___x_255_; lean_object* v_tk_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_ref_254_ = lean_ctor_get(v___y_247_, 5);
v___x_255_ = lean_unsigned_to_nat(2u);
v_tk_256_ = l_Lean_Syntax_getArg(v_x_218_, v___x_255_);
v___x_257_ = lean_unsigned_to_nat(3u);
v___x_258_ = l_Lean_Syntax_getArg(v_x_218_, v___x_257_);
lean_dec(v_x_218_);
v___x_259_ = 0;
v___x_260_ = l_Lean_SourceInfo_fromRef(v_ref_254_, v___x_259_);
v___x_261_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5));
v___x_262_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8));
v___x_263_ = lean_obj_once(&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6, &l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6_once, _init_l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6);
if (lean_obj_tag(v_vis_x3f_246_) == 1)
{
lean_object* v_val_264_; lean_object* v___x_265_; 
v_val_264_ = lean_ctor_get(v_vis_x3f_246_, 0);
lean_inc(v_val_264_);
lean_dec_ref_known(v_vis_x3f_246_, 1);
v___x_265_ = l_Array_mkArray1___redArg(v_val_264_);
v___y_224_ = v___y_248_;
v___y_225_ = v_tk_256_;
v___y_226_ = v___x_250_;
v___y_227_ = v___x_262_;
v___y_228_ = v___x_258_;
v___y_229_ = v___x_261_;
v___y_230_ = v___x_260_;
v___y_231_ = v___x_263_;
v___y_232_ = v___x_265_;
goto v___jp_223_;
}
else
{
lean_object* v___x_266_; 
lean_dec(v_vis_x3f_246_);
v___x_266_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___y_224_ = v___y_248_;
v___y_225_ = v_tk_256_;
v___y_226_ = v___x_250_;
v___y_227_ = v___x_262_;
v___y_228_ = v___x_258_;
v___y_229_ = v___x_261_;
v___y_230_ = v___x_260_;
v___y_231_ = v___x_263_;
v___y_232_ = v___x_266_;
goto v___jp_223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___boxed(lean_object* v_x_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance(v_x_277_, v_a_278_, v_a_279_);
lean_dec_ref(v_a_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1(){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_288_ = l_Lean_Elab_macroAttribute;
v___x_289_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1));
v___x_290_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1));
v___x_291_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___boxed), 3, 0);
v___x_292_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_288_, v___x_289_, v___x_290_, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___boxed(lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1();
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta(lean_object* v_x_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_vis_x3f_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1));
lean_inc(v_x_301_);
v___x_333_ = l_Lean_Syntax_isOfKind(v_x_301_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
lean_dec(v_x_301_);
v___x_334_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_334_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = l_Lean_Syntax_getArg(v_x_301_, v___x_335_);
v___x_337_ = l_Lean_Syntax_isNone(v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_336_);
v___x_339_ = l_Lean_Syntax_matchesNull(v___x_336_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; 
lean_dec(v___x_336_);
lean_dec(v_x_301_);
v___x_340_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_340_;
}
else
{
lean_object* v_vis_x3f_341_; lean_object* v___x_342_; 
v_vis_x3f_341_ = l_Lean_Syntax_getArg(v___x_336_, v___x_335_);
lean_dec(v___x_336_);
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v_vis_x3f_341_);
v_vis_x3f_306_ = v___x_342_;
v___y_307_ = v_a_302_;
v___y_308_ = v_a_303_;
goto v___jp_305_;
}
}
else
{
lean_object* v___x_343_; 
lean_dec(v___x_336_);
v___x_343_ = lean_box(0);
v_vis_x3f_306_ = v___x_343_;
v___y_307_ = v_a_302_;
v___y_308_ = v_a_303_;
goto v___jp_305_;
}
}
v___jp_305_:
{
lean_object* v___x_309_; lean_object* v_kind_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_309_ = lean_unsigned_to_nat(1u);
v_kind_310_ = l_Lean_Syntax_getArg(v_x_301_, v___x_309_);
v___x_311_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
lean_inc(v_kind_310_);
v___x_312_ = l_Lean_Syntax_isOfKind(v_kind_310_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
lean_dec(v_kind_310_);
lean_dec(v_vis_x3f_306_);
lean_dec(v_x_301_);
v___x_313_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_313_;
}
else
{
lean_object* v___x_314_; lean_object* v_tk_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_314_ = lean_unsigned_to_nat(2u);
v_tk_315_ = l_Lean_Syntax_getArg(v_x_301_, v___x_314_);
v___x_316_ = lean_unsigned_to_nat(3u);
v___x_317_ = l_Lean_Syntax_getArg(v_x_301_, v___x_316_);
lean_dec(v_x_301_);
v___x_318_ = lean_box(0);
lean_inc(v___x_317_);
v___x_319_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_319_, 0, v___x_317_);
lean_closure_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed), 9, 2);
lean_closure_set(v___x_320_, 0, lean_box(0));
lean_closure_set(v___x_320_, 1, v___x_319_);
v___x_321_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_320_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_323_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval(v_vis_x3f_306_, v_kind_310_, v_tk_315_, v___x_317_, v_a_322_, v___y_307_, v___y_308_);
return v___x_323_;
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec(v___x_317_);
lean_dec(v_tk_315_);
lean_dec(v_kind_310_);
lean_dec(v_vis_x3f_306_);
v_a_324_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_321_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_321_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___boxed(lean_object* v_x_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta(v_x_344_, v_a_345_, v_a_346_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1(){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_356_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_357_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1));
v___x_358_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1));
v___x_359_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___boxed), 4, 0);
v___x_360_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_356_, v___x_357_, v___x_358_, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___boxed(lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1();
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(size_t v_sz_363_, size_t v_i_364_, lean_object* v_bs_365_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = lean_usize_dec_lt(v_i_364_, v_sz_363_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v_bs_365_);
return v___x_367_;
}
else
{
lean_object* v_v_368_; lean_object* v___x_369_; lean_object* v_bs_x27_370_; size_t v___x_371_; size_t v___x_372_; lean_object* v___x_373_; 
v_v_368_ = lean_array_uget(v_bs_365_, v_i_364_);
v___x_369_ = lean_unsigned_to_nat(0u);
v_bs_x27_370_ = lean_array_uset(v_bs_365_, v_i_364_, v___x_369_);
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_add(v_i_364_, v___x_371_);
v___x_373_ = lean_array_uset(v_bs_x27_370_, v_i_364_, v_v_368_);
v_i_364_ = v___x_372_;
v_bs_365_ = v___x_373_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0___boxed(lean_object* v_sz_375_, lean_object* v_i_376_, lean_object* v_bs_377_){
_start:
{
size_t v_sz_boxed_378_; size_t v_i_boxed_379_; lean_object* v_res_380_; 
v_sz_boxed_378_ = lean_unbox_usize(v_sz_375_);
lean_dec(v_sz_375_);
v_i_boxed_379_ = lean_unbox_usize(v_i_376_);
lean_dec(v_i_376_);
v_res_380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(v_sz_boxed_378_, v_i_boxed_379_, v_bs_377_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(size_t v_sz_381_, size_t v_i_382_, lean_object* v_bs_383_){
_start:
{
uint8_t v___x_384_; 
v___x_384_ = lean_usize_dec_lt(v_i_382_, v_sz_381_);
if (v___x_384_ == 0)
{
return v_bs_383_;
}
else
{
lean_object* v_v_385_; lean_object* v___x_386_; lean_object* v_bs_x27_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; size_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; 
v_v_385_ = lean_array_uget(v_bs_383_, v_i_382_);
v___x_386_ = lean_unsigned_to_nat(0u);
v_bs_x27_387_ = lean_array_uset(v_bs_383_, v_i_382_, v___x_386_);
v___x_388_ = l_Lean_TSyntax_getId(v_v_385_);
v___x_389_ = l_Lean_Name_eraseMacroScopes(v___x_388_);
lean_dec(v___x_388_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_v_385_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_382_, v___x_391_);
v___x_393_ = lean_array_uset(v_bs_x27_387_, v_i_382_, v___x_390_);
v_i_382_ = v___x_392_;
v_bs_383_ = v___x_393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1___boxed(lean_object* v_sz_395_, lean_object* v_i_396_, lean_object* v_bs_397_){
_start:
{
size_t v_sz_boxed_398_; size_t v_i_boxed_399_; lean_object* v_res_400_; 
v_sz_boxed_398_ = lean_unbox_usize(v_sz_395_);
lean_dec(v_sz_395_);
v_i_boxed_399_ = lean_unbox_usize(v_i_396_);
lean_dec(v_i_396_);
v_res_400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(v_sz_boxed_398_, v_i_boxed_399_, v_bs_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(uint8_t v___x_401_, lean_object* v_as_402_, size_t v_i_403_, size_t v_stop_404_, lean_object* v_b_405_){
_start:
{
lean_object* v___y_407_; uint8_t v___x_411_; 
v___x_411_ = lean_usize_dec_eq(v_i_403_, v_stop_404_);
if (v___x_411_ == 0)
{
lean_object* v_fst_412_; uint8_t v___x_413_; 
v_fst_412_ = lean_ctor_get(v_b_405_, 0);
v___x_413_ = lean_unbox(v_fst_412_);
if (v___x_413_ == 0)
{
lean_object* v_snd_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_422_; 
v_snd_414_ = lean_ctor_get(v_b_405_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v_b_405_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v_b_405_, 0);
lean_dec(v_unused_423_);
v___x_416_ = v_b_405_;
v_isShared_417_ = v_isSharedCheck_422_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_snd_414_);
lean_dec(v_b_405_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_422_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = lean_box(v___x_401_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_418_);
v___x_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_snd_414_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
v___y_407_ = v___x_420_;
goto v___jp_406_;
}
}
}
else
{
lean_object* v_snd_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_434_; 
v_snd_424_ = lean_ctor_get(v_b_405_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_b_405_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; 
v_unused_435_ = lean_ctor_get(v_b_405_, 0);
lean_dec(v_unused_435_);
v___x_426_ = v_b_405_;
v_isShared_427_ = v_isSharedCheck_434_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snd_424_);
lean_dec(v_b_405_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_434_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_428_ = lean_array_uget_borrowed(v_as_402_, v_i_403_);
lean_inc(v___x_428_);
v___x_429_ = lean_array_push(v_snd_424_, v___x_428_);
v___x_430_ = lean_box(v___x_411_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_429_);
lean_ctor_set(v___x_426_, 0, v___x_430_);
v___x_432_ = v___x_426_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v___x_429_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
v___y_407_ = v___x_432_;
goto v___jp_406_;
}
}
}
}
else
{
return v_b_405_;
}
v___jp_406_:
{
size_t v___x_408_; size_t v___x_409_; 
v___x_408_ = ((size_t)1ULL);
v___x_409_ = lean_usize_add(v_i_403_, v___x_408_);
v_i_403_ = v___x_409_;
v_b_405_ = v___y_407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2___boxed(lean_object* v___x_436_, lean_object* v_as_437_, lean_object* v_i_438_, lean_object* v_stop_439_, lean_object* v_b_440_){
_start:
{
uint8_t v___x_4794__boxed_441_; size_t v_i_boxed_442_; size_t v_stop_boxed_443_; lean_object* v_res_444_; 
v___x_4794__boxed_441_ = lean_unbox(v___x_436_);
v_i_boxed_442_ = lean_unbox_usize(v_i_438_);
lean_dec(v_i_438_);
v_stop_boxed_443_ = lean_unbox_usize(v_stop_439_);
lean_dec(v_stop_439_);
v_res_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_4794__boxed_441_, v_as_437_, v_i_boxed_442_, v_stop_boxed_443_, v_b_440_);
lean_dec_ref(v_as_437_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(lean_object* v_as_484_, size_t v_sz_485_, size_t v_i_486_, lean_object* v_b_487_){
_start:
{
lean_object* v_a_490_; uint8_t v___x_494_; 
v___x_494_ = lean_usize_dec_lt(v_i_486_, v_sz_485_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v_b_487_);
return v___x_495_;
}
else
{
lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_643_; 
v_fst_496_ = lean_ctor_get(v_b_487_, 0);
v_snd_497_ = lean_ctor_get(v_b_487_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_b_487_);
if (v_isSharedCheck_643_ == 0)
{
v___x_499_ = v_b_487_;
v_isShared_500_ = v_isSharedCheck_643_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_snd_497_);
lean_inc(v_fst_496_);
lean_dec(v_b_487_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_643_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___y_502_; lean_object* v_a_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_a_525_ = lean_array_uget_borrowed(v_as_484_, v_i_486_);
v___x_526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1));
lean_inc(v_a_525_);
v___x_527_ = l_Lean_Syntax_isOfKind(v_a_525_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_del_object(v___x_499_);
v___x_528_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v___x_529_; 
lean_dec_ref_known(v___x_528_, 1);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_fst_496_);
lean_ctor_set(v___x_529_, 1, v_snd_497_);
v_a_490_ = v___x_529_;
goto v___jp_489_;
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
v_a_530_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_528_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_528_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = l_Lean_Syntax_getArg(v_a_525_, v___x_538_);
v___x_541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3));
lean_inc(v___x_540_);
v___x_542_ = l_Lean_Syntax_isOfKind(v___x_540_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; uint8_t v___x_544_; 
lean_del_object(v___x_499_);
v___x_543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5));
lean_inc(v___x_540_);
v___x_544_ = l_Lean_Syntax_isOfKind(v___x_540_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; 
lean_dec(v___x_540_);
v___x_545_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v___x_546_; 
lean_dec_ref_known(v___x_545_, 1);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v_fst_496_);
lean_ctor_set(v___x_546_, 1, v_snd_497_);
v_a_490_ = v___x_546_;
goto v___jp_489_;
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
v_a_547_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_545_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = l_Lean_Syntax_getArg(v___x_540_, v___x_539_);
v___x_556_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7));
lean_inc(v___x_555_);
v___x_557_ = l_Lean_Syntax_isOfKind(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_dec(v___x_555_);
lean_dec(v___x_540_);
v___x_558_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v___x_559_; 
lean_dec_ref_known(v___x_558_, 1);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v_fst_496_);
lean_ctor_set(v___x_559_, 1, v_snd_497_);
v_a_490_ = v___x_559_;
goto v___jp_489_;
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
v_a_560_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_558_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_558_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_fst_571_; uint8_t v_snd_572_; lean_object* v_____x_578_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_568_ = lean_unsigned_to_nat(3u);
v___x_569_ = l_Lean_Syntax_getArg(v___x_540_, v___x_568_);
lean_dec(v___x_540_);
v___x_582_ = l_Lean_Syntax_getArg(v___x_555_, v___x_538_);
v___x_583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9));
lean_inc(v___x_582_);
v___x_584_ = l_Lean_Syntax_isOfKind(v___x_582_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11));
v___x_586_ = l_Lean_Syntax_isOfKind(v___x_582_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v_____x_578_ = v_a_588_;
goto v___jp_577_;
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v___x_569_);
lean_dec(v___x_555_);
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
v_a_589_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_587_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_587_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = lean_box(0);
v___x_598_ = 1;
v_fst_571_ = v___x_597_;
v_snd_572_ = v___x_598_;
goto v___jp_570_;
}
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_599_ = l_Lean_Syntax_getArg(v___x_582_, v___x_538_);
v___x_600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v___x_599_);
v___x_601_ = l_Lean_Syntax_isOfKind(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_dec(v___x_599_);
lean_dec(v___x_582_);
v___x_602_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v_____x_578_ = v_a_603_;
goto v___jp_577_;
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v___x_569_);
lean_dec(v___x_555_);
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
v_a_604_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_602_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = l_Lean_Syntax_getArg(v___x_582_, v___x_539_);
lean_dec(v___x_582_);
lean_inc(v___x_612_);
v___x_613_ = l_Lean_Syntax_matchesNull(v___x_612_, v___x_538_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(2u);
v___x_615_ = l_Lean_Syntax_matchesNull(v___x_612_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
lean_dec(v___x_599_);
v___x_616_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_616_, 1);
v_____x_578_ = v_a_617_;
goto v___jp_577_;
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v___x_569_);
lean_dec(v___x_555_);
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
v_a_618_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_616_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_616_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_626_ = l_Lean_TSyntax_getId(v___x_599_);
lean_dec(v___x_599_);
v___x_627_ = l_Lean_Name_eraseMacroScopes(v___x_626_);
lean_dec(v___x_626_);
v___x_628_ = 1;
v_fst_571_ = v___x_627_;
v_snd_572_ = v___x_628_;
goto v___jp_570_;
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
lean_dec(v___x_612_);
v___x_629_ = l_Lean_TSyntax_getId(v___x_599_);
lean_dec(v___x_599_);
v___x_630_ = l_Lean_Name_eraseMacroScopes(v___x_629_);
lean_dec(v___x_629_);
v___x_631_ = 0;
v_fst_571_ = v___x_630_;
v_snd_572_ = v___x_631_;
goto v___jp_570_;
}
}
}
v___jp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_573_ = lean_box(0);
v___x_574_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_574_, 0, v___x_555_);
lean_ctor_set(v___x_574_, 1, v_fst_571_);
lean_ctor_set(v___x_574_, 2, v___x_569_);
lean_ctor_set(v___x_574_, 3, v___x_573_);
lean_ctor_set(v___x_574_, 4, v___x_573_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*5, v_snd_572_);
v___x_575_ = lean_array_push(v_snd_497_, v___x_574_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_fst_496_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v_a_490_ = v___x_576_;
goto v___jp_489_;
}
v___jp_577_:
{
lean_object* v_fst_579_; lean_object* v_snd_580_; uint8_t v___x_581_; 
v_fst_579_ = lean_ctor_get(v_____x_578_, 0);
lean_inc(v_fst_579_);
v_snd_580_ = lean_ctor_get(v_____x_578_, 1);
lean_inc(v_snd_580_);
lean_dec_ref(v_____x_578_);
v___x_581_ = lean_unbox(v_snd_580_);
lean_dec(v_snd_580_);
v_fst_571_ = v_fst_579_;
v_snd_572_ = v___x_581_;
goto v___jp_570_;
}
}
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_632_ = l_Lean_Syntax_getArg(v___x_540_, v___x_539_);
lean_dec(v___x_540_);
v___x_633_ = l_Lean_Syntax_getArgs(v___x_632_);
lean_dec(v___x_632_);
v___x_634_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___x_635_ = lean_array_get_size(v___x_633_);
v___x_636_ = lean_nat_dec_lt(v___x_538_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec_ref(v___x_633_);
v___y_502_ = v___x_634_;
goto v___jp_501_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; lean_object* v_snd_642_; 
v___x_637_ = lean_box(v___x_636_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_634_);
v___x_639_ = ((size_t)0ULL);
v___x_640_ = lean_usize_of_nat(v___x_635_);
v___x_641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_542_, v___x_633_, v___x_639_, v___x_640_, v___x_638_);
lean_dec_ref(v___x_633_);
v_snd_642_ = lean_ctor_get(v___x_641_, 1);
lean_inc(v_snd_642_);
lean_dec_ref(v___x_641_);
v___y_502_ = v_snd_642_;
goto v___jp_501_;
}
}
}
v___jp_501_:
{
size_t v_sz_503_; size_t v___x_504_; lean_object* v___x_505_; 
v_sz_503_ = lean_array_size(v___y_502_);
v___x_504_ = ((size_t)0ULL);
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(v_sz_503_, v___x_504_, v___y_502_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v___x_508_; 
lean_dec_ref_known(v___x_506_, 1);
if (v_isShared_500_ == 0)
{
v___x_508_ = v___x_499_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_fst_496_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_snd_497_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
v_a_490_ = v___x_508_;
goto v___jp_489_;
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_del_object(v___x_499_);
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
v_a_510_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_506_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_506_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v_val_518_; size_t v_sz_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v_val_518_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v___x_505_, 1);
v_sz_519_ = lean_array_size(v_val_518_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(v_sz_519_, v___x_504_, v_val_518_);
v___x_521_ = l_Array_append___redArg(v_fst_496_, v___x_520_);
lean_dec_ref(v___x_520_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_521_);
v___x_523_ = v___x_499_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_snd_497_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
v_a_490_ = v___x_523_;
goto v___jp_489_;
}
}
}
}
}
v___jp_489_:
{
size_t v___x_491_; size_t v___x_492_; 
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_486_, v___x_491_);
v_i_486_ = v___x_492_;
v_b_487_ = v_a_490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___boxed(lean_object* v_as_644_, lean_object* v_sz_645_, lean_object* v_i_646_, lean_object* v_b_647_, lean_object* v___y_648_){
_start:
{
size_t v_sz_boxed_649_; size_t v_i_boxed_650_; lean_object* v_res_651_; 
v_sz_boxed_649_ = lean_unbox_usize(v_sz_645_);
lean_dec(v_sz_645_);
v_i_boxed_650_ = lean_unbox_usize(v_i_646_);
lean_dec(v_i_646_);
v_res_651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_as_644_, v_sz_boxed_649_, v_i_boxed_650_, v_b_647_);
lean_dec_ref(v_as_644_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(size_t v_sz_652_, size_t v_i_653_, lean_object* v_bs_654_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = lean_usize_dec_lt(v_i_653_, v_sz_652_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v_bs_654_);
return v___x_656_;
}
else
{
lean_object* v_v_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_v_657_ = lean_array_uget(v_bs_654_, v_i_653_);
v___x_658_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1));
lean_inc(v_v_657_);
v___x_659_ = l_Lean_Syntax_isOfKind(v_v_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec(v_v_657_);
lean_dec_ref(v_bs_654_);
v___x_660_ = lean_box(0);
return v___x_660_;
}
else
{
lean_object* v___x_661_; lean_object* v_bs_x27_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
v___x_661_ = lean_unsigned_to_nat(0u);
v_bs_x27_662_ = lean_array_uset(v_bs_654_, v_i_653_, v___x_661_);
v___x_663_ = ((size_t)1ULL);
v___x_664_ = lean_usize_add(v_i_653_, v___x_663_);
v___x_665_ = lean_array_uset(v_bs_x27_662_, v_i_653_, v_v_657_);
v_i_653_ = v___x_664_;
v_bs_654_ = v___x_665_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3___boxed(lean_object* v_sz_667_, lean_object* v_i_668_, lean_object* v_bs_669_){
_start:
{
size_t v_sz_boxed_670_; size_t v_i_boxed_671_; lean_object* v_res_672_; 
v_sz_boxed_670_ = lean_unbox_usize(v_sz_667_);
lean_dec(v_sz_667_);
v_i_boxed_671_ = lean_unbox_usize(v_i_668_);
lean_dec(v_i_668_);
v_res_672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(v_sz_boxed_670_, v_i_boxed_671_, v_bs_669_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView(lean_object* v_entries_x3f_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_omitFields_688_; lean_object* v_handlers_689_; lean_object* v___x_692_; lean_object* v_omitFields_693_; lean_object* v___y_695_; 
v___x_692_ = lean_unsigned_to_nat(0u);
v_omitFields_693_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0));
if (lean_obj_tag(v_entries_x3f_683_) == 1)
{
lean_object* v_val_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_val_723_ = lean_ctor_get(v_entries_x3f_683_, 0);
lean_inc_n(v_val_723_, 2);
lean_dec_ref_known(v_entries_x3f_683_, 1);
v___x_724_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
v___x_725_ = l_Lean_Syntax_isOfKind(v_val_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v_val_723_);
v___x_726_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = l_Lean_Syntax_getArg(v_val_723_, v___x_735_);
lean_dec(v_val_723_);
v___x_737_ = l_Lean_Syntax_getArgs(v___x_736_);
lean_dec(v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___x_739_ = lean_array_get_size(v___x_737_);
v___x_740_ = lean_nat_dec_lt(v___x_692_, v___x_739_);
if (v___x_740_ == 0)
{
lean_dec_ref(v___x_737_);
v___y_695_ = v___x_738_;
goto v___jp_694_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; size_t v___x_743_; size_t v___x_744_; lean_object* v___x_745_; lean_object* v_snd_746_; 
v___x_741_ = lean_box(v___x_740_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v___x_738_);
v___x_743_ = ((size_t)0ULL);
v___x_744_ = lean_usize_of_nat(v___x_739_);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_725_, v___x_737_, v___x_743_, v___x_744_, v___x_742_);
lean_dec_ref(v___x_737_);
v_snd_746_ = lean_ctor_get(v___x_745_, 1);
lean_inc(v_snd_746_);
lean_dec_ref(v___x_745_);
v___y_695_ = v_snd_746_;
goto v___jp_694_;
}
}
}
else
{
lean_dec(v_entries_x3f_683_);
v_omitFields_688_ = v_omitFields_693_;
v_handlers_689_ = v_omitFields_693_;
goto v___jp_687_;
}
v___jp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_omitFields_688_);
lean_ctor_set(v___x_690_, 1, v_handlers_689_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
v___jp_694_:
{
size_t v_sz_696_; size_t v___x_697_; lean_object* v___x_698_; 
v_sz_696_ = lean_array_size(v___y_695_);
v___x_697_ = ((size_t)0ULL);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(v_sz_696_, v___x_697_, v___y_695_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v___x_699_; lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v___x_699_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
lean_object* v_val_708_; lean_object* v___x_709_; size_t v_sz_710_; lean_object* v___x_711_; 
v_val_708_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v___x_698_, 1);
v___x_709_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1));
v_sz_710_ = lean_array_size(v_val_708_);
v___x_711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_val_708_, v_sz_710_, v___x_697_, v___x_709_);
lean_dec(v_val_708_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v_fst_713_; lean_object* v_snd_714_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v_fst_713_ = lean_ctor_get(v_a_712_, 0);
lean_inc(v_fst_713_);
v_snd_714_ = lean_ctor_get(v_a_712_, 1);
lean_inc(v_snd_714_);
lean_dec(v_a_712_);
v_omitFields_688_ = v_fst_713_;
v_handlers_689_ = v_snd_714_;
goto v___jp_687_;
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
v_a_715_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_711_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_711_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView___boxed(lean_object* v_entries_x3f_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Elab_ConfigEval_mkEvalConfigItemView(v_entries_x3f_747_, v_a_748_, v_a_749_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4(lean_object* v_as_752_, size_t v_sz_753_, size_t v_i_754_, lean_object* v_b_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_as_752_, v_sz_753_, v_i_754_, v_b_755_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___boxed(lean_object* v_as_760_, lean_object* v_sz_761_, lean_object* v_i_762_, lean_object* v_b_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
size_t v_sz_boxed_767_; size_t v_i_boxed_768_; lean_object* v_res_769_; 
v_sz_boxed_767_ = lean_unbox_usize(v_sz_761_);
lean_dec(v_sz_761_);
v_i_boxed_768_ = lean_unbox_usize(v_i_762_);
lean_dec(v_i_762_);
v_res_769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4(v_as_760_, v_sz_boxed_767_, v_i_boxed_768_, v_b_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec_ref(v_as_760_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd(lean_object* v_x_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v_entries_x3f_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1));
lean_inc(v_x_783_);
v___x_811_ = l_Lean_Syntax_isOfKind(v_x_783_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
lean_dec(v_x_783_);
v___x_812_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_812_;
}
else
{
lean_object* v___x_813_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v_vis_x3f_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v_doc_x3f_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_861_ = l_Lean_Syntax_getArg(v_x_783_, v___x_813_);
v___x_862_ = l_Lean_Syntax_isNone(v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_861_);
v___x_864_ = l_Lean_Syntax_matchesNull(v___x_861_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
lean_dec(v___x_861_);
lean_dec(v_x_783_);
v___x_865_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_865_;
}
else
{
lean_object* v_doc_x3f_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_doc_x3f_866_ = l_Lean_Syntax_getArg(v___x_861_, v___x_813_);
lean_dec(v___x_861_);
v___x_867_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_866_);
v___x_868_ = l_Lean_Syntax_isOfKind(v_doc_x3f_866_, v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
lean_dec(v_doc_x3f_866_);
lean_dec(v_x_783_);
v___x_869_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_869_;
}
else
{
lean_object* v___x_870_; 
v___x_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_870_, 0, v_doc_x3f_866_);
v_doc_x3f_850_ = v___x_870_;
v___y_851_ = v_a_784_;
v___y_852_ = v_a_785_;
goto v___jp_849_;
}
}
}
else
{
lean_object* v___x_871_; 
lean_dec(v___x_861_);
v___x_871_ = lean_box(0);
v_doc_x3f_850_ = v___x_871_;
v___y_851_ = v_a_784_;
v___y_852_ = v_a_785_;
goto v___jp_849_;
}
v___jp_814_:
{
lean_object* v___x_820_; lean_object* v_kind_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_820_ = lean_unsigned_to_nat(2u);
v_kind_821_ = l_Lean_Syntax_getArg(v_x_783_, v___x_820_);
v___x_822_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
lean_inc(v_kind_821_);
v___x_823_ = l_Lean_Syntax_isOfKind(v_kind_821_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; 
lean_dec(v_kind_821_);
lean_dec(v_vis_x3f_817_);
lean_dec(v___y_815_);
lean_dec(v_x_783_);
v___x_824_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_824_;
}
else
{
lean_object* v___x_825_; lean_object* v_fn_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_825_ = lean_unsigned_to_nat(4u);
v_fn_826_ = l_Lean_Syntax_getArg(v_x_783_, v___x_825_);
v___x_827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_fn_826_);
v___x_828_ = l_Lean_Syntax_isOfKind(v_fn_826_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_dec(v_fn_826_);
lean_dec(v_kind_821_);
lean_dec(v_vis_x3f_817_);
lean_dec(v___y_815_);
lean_dec(v_x_783_);
v___x_829_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_829_;
}
else
{
lean_object* v___x_830_; lean_object* v_struct_831_; uint8_t v___x_832_; 
v___x_830_ = lean_unsigned_to_nat(7u);
v_struct_831_ = l_Lean_Syntax_getArg(v_x_783_, v___x_830_);
lean_inc(v_struct_831_);
v___x_832_ = l_Lean_Syntax_isOfKind(v_struct_831_, v___x_827_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; 
lean_dec(v_struct_831_);
lean_dec(v_fn_826_);
lean_dec(v_kind_821_);
lean_dec(v_vis_x3f_817_);
lean_dec(v___y_815_);
lean_dec(v_x_783_);
v___x_833_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_833_;
}
else
{
lean_object* v___x_834_; lean_object* v_tk_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_834_ = lean_unsigned_to_nat(3u);
v_tk_835_ = l_Lean_Syntax_getArg(v_x_783_, v___x_834_);
v___x_836_ = lean_unsigned_to_nat(5u);
v___x_837_ = l_Lean_Syntax_getArg(v_x_783_, v___x_836_);
v___x_838_ = lean_unsigned_to_nat(8u);
v___x_839_ = l_Lean_Syntax_getArg(v_x_783_, v___x_838_);
lean_dec(v_x_783_);
v___x_840_ = l_Lean_Syntax_isNone(v___x_839_);
if (v___x_840_ == 0)
{
uint8_t v___x_841_; 
lean_inc(v___x_839_);
v___x_841_ = l_Lean_Syntax_matchesNull(v___x_839_, v___y_816_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
lean_dec(v___x_839_);
lean_dec(v___x_837_);
lean_dec(v_tk_835_);
lean_dec(v_struct_831_);
lean_dec(v_fn_826_);
lean_dec(v_kind_821_);
lean_dec(v_vis_x3f_817_);
lean_dec(v___y_815_);
v___x_842_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_842_;
}
else
{
lean_object* v_entries_x3f_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_entries_x3f_843_ = l_Lean_Syntax_getArg(v___x_839_, v___x_813_);
lean_dec(v___x_839_);
v___x_844_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_843_);
v___x_845_ = l_Lean_Syntax_isOfKind(v_entries_x3f_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; 
lean_dec(v_entries_x3f_843_);
lean_dec(v___x_837_);
lean_dec(v_tk_835_);
lean_dec(v_struct_831_);
lean_dec(v_fn_826_);
lean_dec(v_kind_821_);
lean_dec(v_vis_x3f_817_);
lean_dec(v___y_815_);
v___x_846_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_846_;
}
else
{
lean_object* v___x_847_; 
v___x_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_847_, 0, v_entries_x3f_843_);
v___y_788_ = v___y_815_;
v___y_789_ = v_vis_x3f_817_;
v___y_790_ = v_fn_826_;
v___y_791_ = v_struct_831_;
v___y_792_ = v_tk_835_;
v___y_793_ = v___x_837_;
v___y_794_ = v_kind_821_;
v_entries_x3f_795_ = v___x_847_;
v___y_796_ = v___y_818_;
v___y_797_ = v___y_819_;
goto v___jp_787_;
}
}
}
else
{
lean_object* v___x_848_; 
lean_dec(v___x_839_);
v___x_848_ = lean_box(0);
v___y_788_ = v___y_815_;
v___y_789_ = v_vis_x3f_817_;
v___y_790_ = v_fn_826_;
v___y_791_ = v_struct_831_;
v___y_792_ = v_tk_835_;
v___y_793_ = v___x_837_;
v___y_794_ = v_kind_821_;
v_entries_x3f_795_ = v___x_848_;
v___y_796_ = v___y_818_;
v___y_797_ = v___y_819_;
goto v___jp_787_;
}
}
}
}
}
v___jp_849_:
{
lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = l_Lean_Syntax_getArg(v_x_783_, v___x_853_);
v___x_855_ = l_Lean_Syntax_isNone(v___x_854_);
if (v___x_855_ == 0)
{
uint8_t v___x_856_; 
lean_inc(v___x_854_);
v___x_856_ = l_Lean_Syntax_matchesNull(v___x_854_, v___x_853_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
lean_dec(v___x_854_);
lean_dec(v_doc_x3f_850_);
lean_dec(v_x_783_);
v___x_857_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_857_;
}
else
{
lean_object* v_vis_x3f_858_; lean_object* v___x_859_; 
v_vis_x3f_858_ = l_Lean_Syntax_getArg(v___x_854_, v___x_813_);
lean_dec(v___x_854_);
v___x_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_859_, 0, v_vis_x3f_858_);
v___y_815_ = v_doc_x3f_850_;
v___y_816_ = v___x_853_;
v_vis_x3f_817_ = v___x_859_;
v___y_818_ = v___y_851_;
v___y_819_ = v___y_852_;
goto v___jp_814_;
}
}
else
{
lean_object* v___x_860_; 
lean_dec(v___x_854_);
v___x_860_ = lean_box(0);
v___y_815_ = v_doc_x3f_850_;
v___y_816_ = v___x_853_;
v_vis_x3f_817_ = v___x_860_;
v___y_818_ = v___y_851_;
v___y_819_ = v___y_852_;
goto v___jp_814_;
}
}
}
v___jp_787_:
{
lean_object* v_binders_798_; lean_object* v___x_799_; 
v_binders_798_ = l_Lean_Syntax_getArgs(v___y_793_);
lean_dec(v___y_793_);
v___x_799_ = l_Lean_Elab_ConfigEval_mkEvalConfigItemView(v_entries_x3f_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_801_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
v___x_801_ = l_Lean_Elab_ConfigEval_defEvalConfigItem(v___y_788_, v___y_789_, v___y_794_, v___y_792_, v___y_791_, v___y_790_, v_binders_798_, v_a_800_, v___y_796_, v___y_797_);
return v___x_801_;
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v_binders_798_);
lean_dec(v___y_794_);
lean_dec(v___y_792_);
lean_dec(v___y_791_);
lean_dec(v___y_790_);
lean_dec(v___y_789_);
lean_dec(v___y_788_);
v_a_802_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_799_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_799_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___boxed(lean_object* v_x_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd(v_x_872_, v_a_873_, v_a_874_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1(){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_884_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_885_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1));
v___x_886_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1));
v___x_887_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___boxed), 4, 0);
v___x_888_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_884_, v___x_885_, v___x_886_, v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___boxed(lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1();
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd(lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_897_ = lean_unsigned_to_nat(2u);
v___x_898_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_896_, v___x_897_, v_a_892_, v_a_893_, v_a_894_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___boxed(lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd(v_a_899_, v_a_900_, v_a_901_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
return v_res_903_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___boxed), 4, 0);
v___x_905_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1(){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1));
v___x_908_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0);
v___x_909_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_907_, v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___boxed(lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1();
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(size_t v_sz_912_, size_t v_i_913_, lean_object* v_bs_914_){
_start:
{
uint8_t v___x_915_; 
v___x_915_ = lean_usize_dec_lt(v_i_913_, v_sz_912_);
if (v___x_915_ == 0)
{
return v_bs_914_;
}
else
{
lean_object* v_v_916_; lean_object* v___x_917_; lean_object* v_bs_x27_918_; size_t v___x_919_; size_t v___x_920_; lean_object* v___x_921_; 
v_v_916_ = lean_array_uget(v_bs_914_, v_i_913_);
v___x_917_ = lean_unsigned_to_nat(0u);
v_bs_x27_918_ = lean_array_uset(v_bs_914_, v_i_913_, v___x_917_);
v___x_919_ = ((size_t)1ULL);
v___x_920_ = lean_usize_add(v_i_913_, v___x_919_);
v___x_921_ = lean_array_uset(v_bs_x27_918_, v_i_913_, v_v_916_);
v_i_913_ = v___x_920_;
v_bs_914_ = v___x_921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0___boxed(lean_object* v_sz_923_, lean_object* v_i_924_, lean_object* v_bs_925_){
_start:
{
size_t v_sz_boxed_926_; size_t v_i_boxed_927_; lean_object* v_res_928_; 
v_sz_boxed_926_ = lean_unbox_usize(v_sz_923_);
lean_dec(v_sz_923_);
v_i_boxed_927_ = lean_unbox_usize(v_i_924_);
lean_dec(v_i_924_);
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_boxed_926_, v_i_boxed_927_, v_bs_925_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(lean_object* v_stx_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1));
lean_inc(v_stx_954_);
v___x_958_ = l_Lean_Syntax_isOfKind(v_stx_954_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_959_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3));
lean_inc(v_stx_954_);
v___x_960_ = l_Lean_Syntax_isOfKind(v_stx_954_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_961_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5));
lean_inc(v_stx_954_);
v___x_962_ = l_Lean_Syntax_isOfKind(v_stx_954_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7));
lean_inc(v_stx_954_);
v___x_964_ = l_Lean_Syntax_isOfKind(v_stx_954_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_966_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_954_, v___x_965_, v_a_955_, v_a_956_);
lean_dec(v_stx_954_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = l_Lean_Syntax_getArg(v_stx_954_, v___x_968_);
v___x_970_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_969_);
v___x_971_ = l_Lean_Syntax_matchesNull(v___x_969_, v___x_970_);
if (v___x_971_ == 0)
{
uint8_t v___x_972_; 
v___x_972_ = l_Lean_Syntax_matchesNull(v___x_969_, v___x_967_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_974_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_954_, v___x_973_, v_a_955_, v_a_956_);
lean_dec(v_stx_954_);
return v___x_974_;
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_975_ = l_Lean_mkHole(v_stx_954_, v___x_971_);
lean_dec(v_stx_954_);
v___x_976_ = lean_mk_empty_array_with_capacity(v___x_968_);
v___x_977_ = lean_array_push(v___x_976_, v___x_975_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_a_956_);
return v___x_978_;
}
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_979_ = l_Lean_Syntax_getArg(v___x_969_, v___x_967_);
lean_dec(v___x_969_);
v___x_980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v___x_979_);
v___x_981_ = l_Lean_Syntax_isOfKind(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec(v___x_979_);
v___x_982_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_983_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_954_, v___x_982_, v_a_955_, v_a_956_);
lean_dec(v_stx_954_);
return v___x_983_;
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
lean_dec(v_stx_954_);
v___x_984_ = lean_mk_empty_array_with_capacity(v___x_968_);
v___x_985_ = lean_array_push(v___x_984_, v___x_979_);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v_a_956_);
return v___x_986_;
}
}
}
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_987_ = lean_unsigned_to_nat(2u);
v___x_988_ = l_Lean_Syntax_getArg(v_stx_954_, v___x_987_);
v___x_989_ = l_Lean_Syntax_matchesNull(v___x_988_, v___x_987_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_991_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_954_, v___x_990_, v_a_955_, v_a_956_);
lean_dec(v_stx_954_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v_ids_994_; size_t v_sz_995_; size_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_992_ = lean_unsigned_to_nat(1u);
v___x_993_ = l_Lean_Syntax_getArg(v_stx_954_, v___x_992_);
lean_dec(v_stx_954_);
v_ids_994_ = l_Lean_Syntax_getArgs(v___x_993_);
lean_dec(v___x_993_);
v_sz_995_ = lean_array_size(v_ids_994_);
v___x_996_ = ((size_t)0ULL);
v___x_997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_995_, v___x_996_, v_ids_994_);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v_a_956_);
return v___x_998_;
}
}
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___y_1002_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_999_ = lean_unsigned_to_nat(1u);
v___x_1000_ = l_Lean_Syntax_getArg(v_stx_954_, v___x_999_);
v___x_1008_ = lean_unsigned_to_nat(2u);
v___x_1009_ = l_Lean_Syntax_getArg(v_stx_954_, v___x_1008_);
v___x_1010_ = l_Lean_Syntax_isNone(v___x_1009_);
if (v___x_1010_ == 0)
{
uint8_t v___x_1011_; 
v___x_1011_ = l_Lean_Syntax_matchesNull(v___x_1009_, v___x_1008_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_dec(v___x_1000_);
v___x_1012_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_1013_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_954_, v___x_1012_, v_a_955_, v_a_956_);
lean_dec(v_stx_954_);
return v___x_1013_;
}
else
{
lean_dec(v_stx_954_);
v___y_1002_ = v_a_956_;
goto v___jp_1001_;
}
}
else
{
lean_dec(v___x_1009_);
lean_dec(v_stx_954_);
v___y_1002_ = v_a_956_;
goto v___jp_1001_;
}
v___jp_1001_:
{
lean_object* v_ids_1003_; size_t v_sz_1004_; size_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_ids_1003_ = l_Lean_Syntax_getArgs(v___x_1000_);
lean_dec(v___x_1000_);
v_sz_1004_ = lean_array_size(v_ids_1003_);
v___x_1005_ = ((size_t)0ULL);
v___x_1006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_1004_, v___x_1005_, v_ids_1003_);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___y_1002_);
return v___x_1007_;
}
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___y_1017_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1014_ = lean_unsigned_to_nat(1u);
v___x_1015_ = l_Lean_Syntax_getArg(v_stx_954_, v___x_1014_);
v___x_1023_ = lean_unsigned_to_nat(2u);
v___x_1024_ = l_Lean_Syntax_getArg(v_stx_954_, v___x_1023_);
v___x_1025_ = l_Lean_Syntax_isNone(v___x_1024_);
if (v___x_1025_ == 0)
{
uint8_t v___x_1026_; 
v___x_1026_ = l_Lean_Syntax_matchesNull(v___x_1024_, v___x_1023_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec(v___x_1015_);
v___x_1027_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_1028_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_954_, v___x_1027_, v_a_955_, v_a_956_);
lean_dec(v_stx_954_);
return v___x_1028_;
}
else
{
lean_dec(v_stx_954_);
v___y_1017_ = v_a_956_;
goto v___jp_1016_;
}
}
else
{
lean_dec(v___x_1024_);
lean_dec(v_stx_954_);
v___y_1017_ = v_a_956_;
goto v___jp_1016_;
}
v___jp_1016_:
{
lean_object* v_ids_1018_; size_t v_sz_1019_; size_t v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_ids_1018_ = l_Lean_Syntax_getArgs(v___x_1015_);
lean_dec(v___x_1015_);
v_sz_1019_ = lean_array_size(v_ids_1018_);
v___x_1020_ = ((size_t)0ULL);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_1019_, v___x_1020_, v_ids_1018_);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v___y_1017_);
return v___x_1022_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___boxed(lean_object* v_stx_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(v_stx_1029_, v_a_1030_, v_a_1031_);
lean_dec_ref(v_a_1030_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(lean_object* v_as_1033_, size_t v_i_1034_, size_t v_stop_1035_, lean_object* v_b_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
uint8_t v___x_1039_; 
v___x_1039_ = lean_usize_dec_eq(v_i_1034_, v_stop_1035_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_array_uget_borrowed(v_as_1033_, v_i_1034_);
lean_inc(v___x_1040_);
v___x_1041_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(v___x_1040_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v_a_1043_; lean_object* v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
v_a_1043_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1041_, 2);
v___x_1044_ = l_Array_append___redArg(v_b_1036_, v_a_1042_);
lean_dec(v_a_1042_);
v___x_1045_ = ((size_t)1ULL);
v___x_1046_ = lean_usize_add(v_i_1034_, v___x_1045_);
v_i_1034_ = v___x_1046_;
v_b_1036_ = v___x_1044_;
v___y_1038_ = v_a_1043_;
goto _start;
}
else
{
lean_dec_ref(v_b_1036_);
return v___x_1041_;
}
}
else
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_b_1036_);
lean_ctor_set(v___x_1048_, 1, v___y_1038_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3___boxed(lean_object* v_as_1049_, lean_object* v_i_1050_, lean_object* v_stop_1051_, lean_object* v_b_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
size_t v_i_boxed_1055_; size_t v_stop_boxed_1056_; lean_object* v_res_1057_; 
v_i_boxed_1055_ = lean_unbox_usize(v_i_1050_);
lean_dec(v_i_1050_);
v_stop_boxed_1056_ = lean_unbox_usize(v_stop_1051_);
lean_dec(v_stop_1051_);
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_as_1049_, v_i_boxed_1055_, v_stop_boxed_1056_, v_b_1052_, v___y_1053_, v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec_ref(v_as_1049_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(size_t v_sz_1058_, size_t v_i_1059_, lean_object* v_bs_1060_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = lean_usize_dec_lt(v_i_1059_, v_sz_1058_);
if (v___x_1061_ == 0)
{
return v_bs_1060_;
}
else
{
lean_object* v_v_1062_; lean_object* v___x_1063_; lean_object* v_bs_x27_1064_; size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v_v_1062_ = lean_array_uget(v_bs_1060_, v_i_1059_);
v___x_1063_ = lean_unsigned_to_nat(0u);
v_bs_x27_1064_ = lean_array_uset(v_bs_1060_, v_i_1059_, v___x_1063_);
v___x_1065_ = ((size_t)1ULL);
v___x_1066_ = lean_usize_add(v_i_1059_, v___x_1065_);
v___x_1067_ = lean_array_uset(v_bs_x27_1064_, v_i_1059_, v_v_1062_);
v_i_1059_ = v___x_1066_;
v_bs_1060_ = v___x_1067_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2___boxed(lean_object* v_sz_1069_, lean_object* v_i_1070_, lean_object* v_bs_1071_){
_start:
{
size_t v_sz_boxed_1072_; size_t v_i_boxed_1073_; lean_object* v_res_1074_; 
v_sz_boxed_1072_ = lean_unbox_usize(v_sz_1069_);
lean_dec(v_sz_1069_);
v_i_boxed_1073_ = lean_unbox_usize(v_i_1070_);
lean_dec(v_i_1070_);
v_res_1074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(v_sz_boxed_1072_, v_i_boxed_1073_, v_bs_1071_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(size_t v_sz_1075_, size_t v_i_1076_, lean_object* v_bs_1077_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_lt(v_i_1076_, v_sz_1075_);
if (v___x_1078_ == 0)
{
return v_bs_1077_;
}
else
{
lean_object* v_v_1079_; lean_object* v___x_1080_; lean_object* v_bs_x27_1081_; size_t v___x_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v_v_1079_ = lean_array_uget(v_bs_1077_, v_i_1076_);
v___x_1080_ = lean_unsigned_to_nat(0u);
v_bs_x27_1081_ = lean_array_uset(v_bs_1077_, v_i_1076_, v___x_1080_);
v___x_1082_ = ((size_t)1ULL);
v___x_1083_ = lean_usize_add(v_i_1076_, v___x_1082_);
v___x_1084_ = lean_array_uset(v_bs_x27_1081_, v_i_1076_, v_v_1079_);
v_i_1076_ = v___x_1083_;
v_bs_1077_ = v___x_1084_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0___boxed(lean_object* v_sz_1086_, lean_object* v_i_1087_, lean_object* v_bs_1088_){
_start:
{
size_t v_sz_boxed_1089_; size_t v_i_boxed_1090_; lean_object* v_res_1091_; 
v_sz_boxed_1089_ = lean_unbox_usize(v_sz_1086_);
lean_dec(v_sz_1086_);
v_i_boxed_1090_ = lean_unbox_usize(v_i_1087_);
lean_dec(v_i_1087_);
v_res_1091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_boxed_1089_, v_i_boxed_1090_, v_bs_1088_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(size_t v_sz_1092_, size_t v_i_1093_, lean_object* v_bs_1094_){
_start:
{
uint8_t v___x_1095_; 
v___x_1095_ = lean_usize_dec_lt(v_i_1093_, v_sz_1092_);
if (v___x_1095_ == 0)
{
return v_bs_1094_;
}
else
{
lean_object* v_v_1096_; lean_object* v___x_1097_; lean_object* v_bs_x27_1098_; size_t v___x_1099_; size_t v___x_1100_; lean_object* v___x_1101_; 
v_v_1096_ = lean_array_uget(v_bs_1094_, v_i_1093_);
v___x_1097_ = lean_unsigned_to_nat(0u);
v_bs_x27_1098_ = lean_array_uset(v_bs_1094_, v_i_1093_, v___x_1097_);
v___x_1099_ = ((size_t)1ULL);
v___x_1100_ = lean_usize_add(v_i_1093_, v___x_1099_);
v___x_1101_ = lean_array_uset(v_bs_x27_1098_, v_i_1093_, v_v_1096_);
v_i_1093_ = v___x_1100_;
v_bs_1094_ = v___x_1101_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1___boxed(lean_object* v_sz_1103_, lean_object* v_i_1104_, lean_object* v_bs_1105_){
_start:
{
size_t v_sz_boxed_1106_; size_t v_i_boxed_1107_; lean_object* v_res_1108_; 
v_sz_boxed_1106_ = lean_unbox_usize(v_sz_1103_);
lean_dec(v_sz_1103_);
v_i_boxed_1107_ = lean_unbox_usize(v_i_1104_);
lean_dec(v_i_1104_);
v_res_1108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(v_sz_boxed_1106_, v_i_boxed_1107_, v_bs_1105_);
return v_res_1108_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6));
v___x_1118_ = l_String_toRawSubstring_x27(v___x_1117_);
return v___x_1118_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25));
v___x_1159_ = l_String_toRawSubstring_x27(v___x_1158_);
return v___x_1159_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53));
v___x_1232_ = l_String_toRawSubstring_x27(v___x_1231_);
return v___x_1232_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56));
v___x_1236_ = l_String_toRawSubstring_x27(v___x_1235_);
return v___x_1236_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59));
v___x_1241_ = l_String_toRawSubstring_x27(v___x_1240_);
return v___x_1241_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74));
v___x_1273_ = l_Lean_mkIdent(v___x_1272_);
return v___x_1273_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77));
v___x_1278_ = l_Lean_mkIdent(v___x_1277_);
return v___x_1278_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80));
v___x_1283_ = l_Lean_mkIdent(v___x_1282_);
return v___x_1283_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84));
v___x_1292_ = l_String_toRawSubstring_x27(v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92));
v___x_1312_ = l_String_toRawSubstring_x27(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98));
v___x_1324_ = l_String_toRawSubstring_x27(v___x_1323_);
return v___x_1324_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73));
v___x_1330_ = l_String_toRawSubstring_x27(v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(lean_object* v_monad_1348_, lean_object* v_mkMonadAdapt_1349_, lean_object* v_logExceptionsDefault_1350_, lean_object* v_mkLogExceptionsTerm_1351_, lean_object* v_doc_x3f_1352_, lean_object* v_vis_x3f_1353_, lean_object* v_tk_1354_, lean_object* v_elabName_1355_, lean_object* v_type_1356_, lean_object* v_binders_1357_, lean_object* v_entries_x3f_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; size_t v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; size_t v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; size_t v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; size_t v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; size_t v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; size_t v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v_a_1674_; lean_object* v_a_1675_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0));
v___x_1363_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0));
v___x_1364_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1));
v___x_1777_ = lean_array_get_size(v_binders_1357_);
v___x_1778_ = lean_nat_dec_lt(v___x_1361_, v___x_1777_);
if (v___x_1778_ == 0)
{
v_a_1674_ = v___x_1362_;
v_a_1675_ = v_a_1360_;
goto v___jp_1673_;
}
else
{
size_t v___x_1779_; size_t v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = ((size_t)0ULL);
v___x_1780_ = lean_usize_of_nat(v___x_1777_);
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_binders_1357_, v___x_1779_, v___x_1780_, v___x_1362_, v_a_1359_, v_a_1360_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v_a_1783_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
v_a_1783_ = lean_ctor_get(v___x_1781_, 1);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1781_, 2);
v_a_1674_ = v_a_1782_;
v_a_1675_ = v_a_1783_;
goto v___jp_1673_;
}
else
{
lean_object* v_a_1784_; lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v_entries_x3f_1358_);
lean_dec_ref(v_binders_1357_);
lean_dec(v_type_1356_);
lean_dec(v_elabName_1355_);
lean_dec(v_tk_1354_);
lean_dec(v_vis_x3f_1353_);
lean_dec(v_doc_x3f_1352_);
lean_dec_ref(v_mkLogExceptionsTerm_1351_);
lean_dec(v_logExceptionsDefault_1350_);
lean_dec_ref(v_mkMonadAdapt_1349_);
lean_dec(v_monad_1348_);
v_a_1784_ = lean_ctor_get(v___x_1781_, 0);
v_a_1785_ = lean_ctor_get(v___x_1781_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1781_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_inc(v_a_1784_);
lean_dec(v___x_1781_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1784_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
v___jp_1365_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; size_t v_sz_1420_; lean_object* v___x_1421_; size_t v_sz_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_inc_ref_n(v___y_1400_, 2);
v___x_1402_ = l_Array_append___redArg(v___y_1400_, v___y_1401_);
lean_dec_ref(v___y_1401_);
lean_inc_n(v___y_1396_, 18);
lean_inc_n(v___y_1366_, 77);
v___x_1403_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1403_, 0, v___y_1366_);
lean_ctor_set(v___x_1403_, 1, v___y_1396_);
lean_ctor_set(v___x_1403_, 2, v___x_1402_);
lean_inc_n(v___y_1369_, 22);
v___x_1404_ = l_Lean_Syntax_node7(v___y_1366_, v___y_1393_, v___y_1392_, v___y_1369_, v___x_1403_, v___y_1369_, v___y_1369_, v___y_1369_, v___y_1369_);
v___x_1405_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1));
lean_inc_ref_n(v___y_1375_, 4);
v___x_1406_ = l_Lean_Name_mkStr4(v___x_1363_, v___x_1364_, v___y_1375_, v___x_1405_);
v___x_1407_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2));
v___x_1408_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___y_1366_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
v___x_1409_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3));
v___x_1410_ = l_Lean_Name_mkStr4(v___x_1363_, v___x_1364_, v___y_1375_, v___x_1409_);
lean_inc_n(v___y_1387_, 2);
v___x_1411_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1411_, 0, v___y_1387_);
lean_ctor_set(v___x_1411_, 1, v___y_1396_);
lean_ctor_set(v___x_1411_, 2, v___x_1362_);
v___x_1412_ = lean_unsigned_to_nat(2u);
v___x_1413_ = lean_mk_empty_array_with_capacity(v___x_1412_);
v___x_1414_ = lean_array_push(v___x_1413_, v_elabName_1355_);
v___x_1415_ = lean_array_push(v___x_1414_, v___x_1411_);
v___x_1416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1416_, 0, v___y_1387_);
lean_ctor_set(v___x_1416_, 1, v___x_1410_);
lean_ctor_set(v___x_1416_, 2, v___x_1415_);
v___x_1417_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4));
v___x_1418_ = l_Lean_Name_mkStr4(v___x_1363_, v___x_1364_, v___y_1375_, v___x_1417_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(v___y_1379_, v___y_1394_, v_binders_1357_);
v_sz_1420_ = lean_array_size(v___x_1419_);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(v_sz_1420_, v___y_1394_, v___x_1419_);
v_sz_1422_ = lean_array_size(v___x_1421_);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_1422_, v___y_1394_, v___x_1421_);
v___x_1424_ = l_Array_append___redArg(v___y_1400_, v___x_1423_);
lean_dec_ref(v___x_1423_);
v___x_1425_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1));
lean_inc_ref(v___y_1386_);
v___x_1426_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___y_1366_);
lean_ctor_set(v___x_1426_, 1, v___y_1386_);
v___x_1427_ = l_Lean_Syntax_node1(v___y_1366_, v___y_1396_, v___y_1374_);
v___x_1428_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5));
v___x_1429_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___y_1366_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7);
v___x_1431_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9));
lean_inc_n(v___y_1370_, 5);
lean_inc_n(v___y_1389_, 5);
v___x_1432_ = l_Lean_addMacroScope(v___y_1389_, v___x_1431_, v___y_1370_);
lean_inc_n(v___y_1397_, 5);
v___x_1433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___y_1397_);
v___x_1434_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10));
lean_inc_n(v___y_1388_, 8);
v___x_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
lean_ctor_set(v___x_1435_, 1, v___y_1388_);
v___x_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1433_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1437_, 0, v___y_1366_);
lean_ctor_set(v___x_1437_, 1, v___x_1430_);
lean_ctor_set(v___x_1437_, 2, v___x_1432_);
lean_ctor_set(v___x_1437_, 3, v___x_1436_);
lean_inc_ref_n(v___x_1429_, 4);
v___x_1438_ = l_Lean_Syntax_node2(v___y_1366_, v___y_1396_, v___x_1429_, v___x_1437_);
lean_inc_ref(v___y_1382_);
v___x_1439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___y_1366_);
lean_ctor_set(v___x_1439_, 1, v___y_1382_);
lean_inc_ref_n(v___x_1439_, 3);
lean_inc_ref_n(v___x_1426_, 3);
v___x_1440_ = l_Lean_Syntax_node5(v___y_1366_, v___x_1425_, v___x_1426_, v___x_1427_, v___x_1438_, v___y_1369_, v___x_1439_);
v___x_1441_ = lean_array_push(v___x_1424_, v___x_1440_);
v___x_1442_ = l_Lean_Syntax_node1(v___y_1366_, v___y_1396_, v___y_1395_);
lean_inc_n(v_type_1356_, 2);
v___x_1443_ = l_Lean_Syntax_node2(v___y_1366_, v___y_1396_, v___x_1429_, v_type_1356_);
v___x_1444_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12));
lean_inc_ref(v___y_1377_);
v___x_1445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___y_1366_);
lean_ctor_set(v___x_1445_, 1, v___y_1377_);
v___x_1446_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14));
v___x_1447_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16));
v___x_1448_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17));
v___x_1449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1366_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18));
v___x_1451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___y_1366_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
lean_inc_ref(v___x_1451_);
lean_inc_ref(v___x_1449_);
v___x_1452_ = l_Lean_Syntax_node2(v___y_1366_, v___x_1447_, v___x_1449_, v___x_1451_);
v___x_1453_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20));
v___x_1454_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22));
v___x_1455_ = l_Lean_Syntax_node1(v___y_1366_, v___x_1454_, v___y_1369_);
v___x_1456_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24));
v___x_1457_ = l_Lean_Syntax_node1(v___y_1366_, v___x_1456_, v___y_1369_);
v___x_1458_ = l_Lean_Syntax_node6(v___y_1366_, v___x_1453_, v___x_1449_, v___y_1369_, v___x_1455_, v___x_1457_, v___y_1369_, v___x_1451_);
v___x_1459_ = l_Lean_Syntax_node2(v___y_1366_, v___x_1446_, v___x_1452_, v___x_1458_);
lean_inc_ref_n(v___x_1445_, 5);
v___x_1460_ = l_Lean_Syntax_node2(v___y_1366_, v___x_1444_, v___x_1445_, v___x_1459_);
v___x_1461_ = l_Lean_Syntax_node1(v___y_1366_, v___y_1396_, v___x_1460_);
v___x_1462_ = l_Lean_Syntax_node5(v___y_1366_, v___x_1425_, v___x_1426_, v___x_1442_, v___x_1443_, v___x_1461_, v___x_1439_);
v___x_1463_ = lean_array_push(v___x_1441_, v___x_1462_);
v___x_1464_ = l_Lean_Syntax_node1(v___y_1366_, v___y_1396_, v___y_1398_);
v___x_1465_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26);
v___x_1466_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27));
v___x_1467_ = l_Lean_addMacroScope(v___y_1389_, v___x_1466_, v___y_1370_);
v___x_1468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___y_1397_);
v___x_1469_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29));
v___x_1470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
lean_ctor_set(v___x_1470_, 1, v___y_1388_);
v___x_1471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1468_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1472_, 0, v___y_1366_);
lean_ctor_set(v___x_1472_, 1, v___x_1465_);
lean_ctor_set(v___x_1472_, 2, v___x_1467_);
lean_ctor_set(v___x_1472_, 3, v___x_1471_);
v___x_1473_ = l_Lean_Syntax_node2(v___y_1366_, v___y_1396_, v___x_1429_, v___x_1472_);
v___x_1474_ = l_Lean_Syntax_node2(v___y_1366_, v___x_1444_, v___x_1445_, v_logExceptionsDefault_1350_);
v___x_1475_ = l_Lean_Syntax_node1(v___y_1366_, v___y_1396_, v___x_1474_);
v___x_1476_ = l_Lean_Syntax_node5(v___y_1366_, v___x_1425_, v___x_1426_, v___x_1464_, v___x_1473_, v___x_1475_, v___x_1439_);
v___x_1477_ = lean_array_push(v___x_1463_, v___x_1476_);
v___x_1478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1478_, 0, v___y_1366_);
lean_ctor_set(v___x_1478_, 1, v___y_1396_);
lean_ctor_set(v___x_1478_, 2, v___x_1477_);
v___x_1479_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31));
v___x_1480_ = l_Lean_Syntax_node1(v___y_1366_, v___y_1396_, v_type_1356_);
lean_inc(v___x_1480_);
lean_inc_n(v___y_1371_, 4);
v___x_1481_ = l_Lean_Syntax_node2(v___y_1366_, v___y_1371_, v_monad_1348_, v___x_1480_);
v___x_1482_ = l_Lean_Syntax_node2(v___y_1366_, v___x_1479_, v___x_1429_, v___x_1481_);
v___x_1483_ = l_Lean_Syntax_node1(v___y_1366_, v___y_1396_, v___x_1482_);
v___x_1484_ = l_Lean_Syntax_node2(v___y_1366_, v___x_1418_, v___x_1478_, v___x_1483_);
v___x_1485_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32));
v___x_1486_ = l_Lean_Name_mkStr4(v___x_1363_, v___x_1364_, v___y_1375_, v___x_1485_);
v___x_1487_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33));
v___x_1488_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34));
v___x_1489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___y_1366_);
lean_ctor_set(v___x_1489_, 1, v___x_1487_);
v___x_1490_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36));
v___x_1491_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38));
v___x_1492_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40));
v___x_1493_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41));
v___x_1494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___y_1366_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43));
v___x_1496_ = l_Lean_Syntax_node1(v___y_1366_, v___x_1495_, v___y_1369_);
v___x_1497_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45));
v___x_1498_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47));
v___x_1499_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49));
lean_inc_ref(v___y_1380_);
v___x_1500_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1500_, 0, v___y_1366_);
lean_ctor_set(v___x_1500_, 1, v___y_1380_);
lean_ctor_set(v___x_1500_, 2, v___y_1372_);
lean_ctor_set(v___x_1500_, 3, v___y_1388_);
v___x_1501_ = l_Lean_Syntax_node1(v___y_1366_, v___x_1499_, v___x_1500_);
lean_inc_ref_n(v___y_1381_, 5);
v___x_1502_ = l_String_toRawSubstring_x27(v___y_1381_);
v___x_1503_ = l_Lean_Name_mkStr1(v___y_1381_);
v___x_1504_ = l_Lean_addMacroScope(v___y_1389_, v___x_1503_, v___y_1370_);
lean_inc_ref_n(v___y_1376_, 2);
lean_inc_ref_n(v___y_1399_, 2);
v___x_1505_ = l_Lean_Name_mkStr4(v___x_1363_, v___y_1399_, v___y_1376_, v___y_1381_);
lean_inc(v___x_1505_);
v___x_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v___y_1397_);
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
v___x_1508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set(v___x_1508_, 1, v___y_1388_);
v___x_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1506_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1510_, 0, v___y_1366_);
lean_ctor_set(v___x_1510_, 1, v___x_1502_);
lean_ctor_set(v___x_1510_, 2, v___x_1504_);
lean_ctor_set(v___x_1510_, 3, v___x_1509_);
v___x_1511_ = l_Lean_Syntax_node2(v___y_1366_, v___y_1371_, v___x_1510_, v___x_1480_);
v___x_1512_ = l_Lean_Syntax_node2(v___y_1366_, v___x_1479_, v___x_1429_, v___x_1511_);
v___x_1513_ = l_Lean_Syntax_node1(v___y_1366_, v___y_1396_, v___x_1512_);
v___x_1514_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51));
v___x_1515_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52));
v___x_1516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___y_1366_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = l_Lean_Syntax_node2(v___y_1366_, v___x_1514_, v___x_1516_, v___y_1385_);
v___x_1518_ = l_Array_append___redArg(v___y_1400_, v___y_1384_);
lean_dec_ref(v___y_1384_);
v___x_1519_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1519_, 0, v___y_1366_);
lean_ctor_set(v___x_1519_, 1, v___y_1396_);
lean_ctor_set(v___x_1519_, 2, v___x_1518_);
v___x_1520_ = l_Lean_Syntax_node2(v___y_1366_, v___y_1371_, v___x_1517_, v___x_1519_);
v___x_1521_ = l_Lean_Syntax_node5(v___y_1366_, v___x_1498_, v___x_1501_, v___y_1369_, v___x_1513_, v___x_1445_, v___x_1520_);
v___x_1522_ = l_Lean_Syntax_node1(v___y_1366_, v___x_1497_, v___x_1521_);
lean_inc(v___x_1496_);
lean_inc_ref(v___x_1494_);
v___x_1523_ = l_Lean_Syntax_node4(v___y_1366_, v___x_1492_, v___x_1494_, v___y_1369_, v___x_1496_, v___x_1522_);
v___x_1524_ = l_Lean_Syntax_node2(v___y_1366_, v___x_1491_, v___x_1523_, v___y_1369_);
lean_inc_ref(v___y_1383_);
v___x_1525_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1525_, 0, v___y_1366_);
lean_ctor_set(v___x_1525_, 1, v___y_1383_);
lean_ctor_set(v___x_1525_, 2, v___y_1368_);
lean_ctor_set(v___x_1525_, 3, v___y_1388_);
v___x_1526_ = l_Lean_Syntax_node1(v___y_1366_, v___x_1499_, v___x_1525_);
v___x_1527_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54);
v___x_1528_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55));
v___x_1529_ = l_Lean_Name_mkStr2(v___y_1381_, v___x_1528_);
v___x_1530_ = l_Lean_addMacroScope(v___y_1389_, v___x_1529_, v___y_1370_);
v___x_1531_ = l_Lean_Name_mkStr5(v___x_1363_, v___y_1399_, v___y_1376_, v___y_1381_, v___x_1528_);
v___x_1532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v___y_1397_);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v___y_1388_);
v___x_1534_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1534_, 0, v___y_1366_);
lean_ctor_set(v___x_1534_, 1, v___x_1527_);
lean_ctor_set(v___x_1534_, 2, v___x_1530_);
lean_ctor_set(v___x_1534_, 3, v___x_1533_);
v___x_1535_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57);
v___x_1536_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58));
v___x_1537_ = l_Lean_addMacroScope(v___y_1389_, v___x_1536_, v___y_1370_);
v___x_1538_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1538_, 0, v___y_1366_);
lean_ctor_set(v___x_1538_, 1, v___x_1535_);
lean_ctor_set(v___x_1538_, 2, v___x_1537_);
lean_ctor_set(v___x_1538_, 3, v___y_1388_);
v___x_1539_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60);
v___x_1540_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61));
v___x_1541_ = l_Lean_addMacroScope(v___y_1389_, v___x_1540_, v___y_1370_);
v___x_1542_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62));
v___x_1543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v___y_1397_);
v___x_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v___y_1388_);
v___x_1545_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1545_, 0, v___y_1366_);
lean_ctor_set(v___x_1545_, 1, v___x_1539_);
lean_ctor_set(v___x_1545_, 2, v___x_1541_);
lean_ctor_set(v___x_1545_, 3, v___x_1544_);
v___x_1546_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64));
v___x_1547_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65));
v___x_1548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___y_1366_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
lean_inc_ref(v___x_1548_);
v___x_1549_ = l_Lean_Syntax_node3(v___y_1366_, v___x_1546_, v___x_1548_, v___x_1548_, v_type_1356_);
v___x_1550_ = l_Lean_Syntax_node1(v___y_1366_, v___y_1396_, v___x_1549_);
v___x_1551_ = l_Lean_Syntax_node2(v___y_1366_, v___y_1371_, v___x_1545_, v___x_1550_);
v___x_1552_ = l_Lean_Syntax_node5(v___y_1366_, v___y_1390_, v___x_1426_, v___x_1538_, v___x_1445_, v___x_1551_, v___x_1439_);
v___x_1553_ = l_Lean_Syntax_node1(v___y_1366_, v___y_1396_, v___x_1552_);
v___x_1554_ = l_Lean_Syntax_node2(v___y_1366_, v___y_1371_, v___x_1534_, v___x_1553_);
v___x_1555_ = l_Lean_Syntax_node5(v___y_1366_, v___x_1498_, v___x_1526_, v___y_1369_, v___y_1369_, v___x_1445_, v___x_1554_);
v___x_1556_ = l_Lean_Syntax_node1(v___y_1366_, v___x_1497_, v___x_1555_);
v___x_1557_ = l_Lean_Syntax_node4(v___y_1366_, v___x_1492_, v___x_1494_, v___y_1369_, v___x_1496_, v___x_1556_);
v___x_1558_ = l_Lean_Syntax_node2(v___y_1366_, v___x_1491_, v___x_1557_, v___y_1369_);
v___x_1559_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67));
v___x_1560_ = l_Lean_Syntax_node1(v___y_1366_, v___x_1559_, v___y_1391_);
v___x_1561_ = l_Lean_Syntax_node2(v___y_1366_, v___x_1491_, v___x_1560_, v___y_1369_);
v___x_1562_ = l_Lean_Syntax_node3(v___y_1366_, v___y_1396_, v___x_1524_, v___x_1558_, v___x_1561_);
v___x_1563_ = l_Lean_Syntax_node1(v___y_1366_, v___x_1490_, v___x_1562_);
v___x_1564_ = l_Lean_Syntax_node2(v___y_1366_, v___x_1488_, v___x_1489_, v___x_1563_);
v___x_1565_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70));
v___x_1566_ = l_Lean_Syntax_node2(v___y_1366_, v___x_1565_, v___y_1369_, v___y_1369_);
v___x_1567_ = l_Lean_Syntax_node4(v___y_1366_, v___x_1486_, v___x_1445_, v___x_1564_, v___x_1566_, v___y_1369_);
v___x_1568_ = l_Lean_Syntax_node5(v___y_1366_, v___x_1406_, v___x_1408_, v___x_1416_, v___x_1484_, v___x_1567_, v___y_1369_);
v___x_1569_ = l_Lean_Syntax_node2(v___y_1366_, v___y_1373_, v___x_1404_, v___x_1568_);
v___x_1570_ = l_Lean_Syntax_node2(v___y_1366_, v___y_1396_, v___y_1378_, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___y_1367_);
return v___x_1571_;
}
v___jp_1572_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_inc_ref(v___y_1606_);
v___x_1608_ = l_Array_append___redArg(v___y_1606_, v___y_1607_);
lean_dec_ref(v___y_1607_);
lean_inc(v___y_1602_);
lean_inc(v___y_1573_);
v___x_1609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1609_, 0, v___y_1573_);
lean_ctor_set(v___x_1609_, 1, v___y_1602_);
lean_ctor_set(v___x_1609_, 2, v___x_1608_);
if (lean_obj_tag(v_vis_x3f_1353_) == 1)
{
lean_object* v_val_1610_; lean_object* v___x_1611_; 
v_val_1610_ = lean_ctor_get(v_vis_x3f_1353_, 0);
lean_inc(v_val_1610_);
lean_dec_ref_known(v_vis_x3f_1353_, 1);
v___x_1611_ = l_Array_mkArray1___redArg(v_val_1610_);
v___y_1366_ = v___y_1573_;
v___y_1367_ = v___y_1576_;
v___y_1368_ = v___y_1575_;
v___y_1369_ = v___y_1574_;
v___y_1370_ = v___y_1577_;
v___y_1371_ = v___y_1579_;
v___y_1372_ = v___y_1578_;
v___y_1373_ = v___y_1581_;
v___y_1374_ = v___y_1580_;
v___y_1375_ = v___y_1582_;
v___y_1376_ = v___y_1583_;
v___y_1377_ = v___y_1584_;
v___y_1378_ = v___y_1585_;
v___y_1379_ = v___y_1586_;
v___y_1380_ = v___y_1587_;
v___y_1381_ = v___y_1588_;
v___y_1382_ = v___y_1589_;
v___y_1383_ = v___y_1590_;
v___y_1384_ = v___y_1591_;
v___y_1385_ = v___y_1592_;
v___y_1386_ = v___y_1593_;
v___y_1387_ = v___y_1594_;
v___y_1388_ = v___y_1595_;
v___y_1389_ = v___y_1596_;
v___y_1390_ = v___y_1597_;
v___y_1391_ = v___y_1598_;
v___y_1392_ = v___x_1609_;
v___y_1393_ = v___y_1599_;
v___y_1394_ = v___y_1601_;
v___y_1395_ = v___y_1600_;
v___y_1396_ = v___y_1602_;
v___y_1397_ = v___y_1603_;
v___y_1398_ = v___y_1604_;
v___y_1399_ = v___y_1605_;
v___y_1400_ = v___y_1606_;
v___y_1401_ = v___x_1611_;
goto v___jp_1365_;
}
else
{
lean_object* v___x_1612_; 
lean_dec(v_vis_x3f_1353_);
v___x_1612_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___y_1366_ = v___y_1573_;
v___y_1367_ = v___y_1576_;
v___y_1368_ = v___y_1575_;
v___y_1369_ = v___y_1574_;
v___y_1370_ = v___y_1577_;
v___y_1371_ = v___y_1579_;
v___y_1372_ = v___y_1578_;
v___y_1373_ = v___y_1581_;
v___y_1374_ = v___y_1580_;
v___y_1375_ = v___y_1582_;
v___y_1376_ = v___y_1583_;
v___y_1377_ = v___y_1584_;
v___y_1378_ = v___y_1585_;
v___y_1379_ = v___y_1586_;
v___y_1380_ = v___y_1587_;
v___y_1381_ = v___y_1588_;
v___y_1382_ = v___y_1589_;
v___y_1383_ = v___y_1590_;
v___y_1384_ = v___y_1591_;
v___y_1385_ = v___y_1592_;
v___y_1386_ = v___y_1593_;
v___y_1387_ = v___y_1594_;
v___y_1388_ = v___y_1595_;
v___y_1389_ = v___y_1596_;
v___y_1390_ = v___y_1597_;
v___y_1391_ = v___y_1598_;
v___y_1392_ = v___x_1609_;
v___y_1393_ = v___y_1599_;
v___y_1394_ = v___y_1601_;
v___y_1395_ = v___y_1600_;
v___y_1396_ = v___y_1602_;
v___y_1397_ = v___y_1603_;
v___y_1398_ = v___y_1604_;
v___y_1399_ = v___y_1605_;
v___y_1400_ = v___y_1606_;
v___y_1401_ = v___x_1612_;
goto v___jp_1365_;
}
}
v___jp_1613_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_inc_ref(v___y_1649_);
v___x_1652_ = l_Array_append___redArg(v___y_1649_, v___y_1651_);
lean_dec_ref(v___y_1651_);
lean_inc(v___y_1645_);
lean_inc_n(v___y_1614_, 2);
v___x_1653_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1653_, 0, v___y_1614_);
lean_ctor_set(v___x_1653_, 1, v___y_1645_);
lean_ctor_set(v___x_1653_, 2, v___x_1652_);
v___x_1654_ = lean_unsigned_to_nat(9u);
v___x_1655_ = lean_mk_empty_array_with_capacity(v___x_1654_);
lean_inc(v___y_1616_);
v___x_1656_ = lean_array_push(v___x_1655_, v___y_1616_);
v___x_1657_ = lean_array_push(v___x_1656_, v___y_1650_);
v___x_1658_ = lean_array_push(v___x_1657_, v___y_1627_);
v___x_1659_ = lean_array_push(v___x_1658_, v___y_1620_);
lean_inc(v___y_1635_);
v___x_1660_ = lean_array_push(v___x_1659_, v___y_1635_);
v___x_1661_ = lean_array_push(v___x_1660_, v___y_1644_);
v___x_1662_ = lean_array_push(v___x_1661_, v___y_1631_);
lean_inc(v_type_1356_);
v___x_1663_ = lean_array_push(v___x_1662_, v_type_1356_);
v___x_1664_ = lean_array_push(v___x_1663_, v___x_1653_);
lean_inc(v___y_1619_);
v___x_1665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1665_, 0, v___y_1614_);
lean_ctor_set(v___x_1665_, 1, v___y_1619_);
lean_ctor_set(v___x_1665_, 2, v___x_1664_);
v___x_1666_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71));
lean_inc_ref_n(v___y_1624_, 2);
v___x_1667_ = l_Lean_Name_mkStr4(v___x_1363_, v___x_1364_, v___y_1624_, v___x_1666_);
v___x_1668_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72));
v___x_1669_ = l_Lean_Name_mkStr4(v___x_1363_, v___x_1364_, v___y_1624_, v___x_1668_);
if (lean_obj_tag(v_doc_x3f_1352_) == 1)
{
lean_object* v_val_1670_; lean_object* v___x_1671_; 
v_val_1670_ = lean_ctor_get(v_doc_x3f_1352_, 0);
lean_inc(v_val_1670_);
lean_dec_ref_known(v_doc_x3f_1352_, 1);
v___x_1671_ = l_Array_mkArray1___redArg(v_val_1670_);
v___y_1573_ = v___y_1614_;
v___y_1574_ = v___y_1616_;
v___y_1575_ = v___y_1615_;
v___y_1576_ = v___y_1617_;
v___y_1577_ = v___y_1618_;
v___y_1578_ = v___y_1621_;
v___y_1579_ = v___y_1622_;
v___y_1580_ = v___y_1623_;
v___y_1581_ = v___x_1667_;
v___y_1582_ = v___y_1624_;
v___y_1583_ = v___y_1625_;
v___y_1584_ = v___y_1626_;
v___y_1585_ = v___x_1665_;
v___y_1586_ = v___y_1628_;
v___y_1587_ = v___y_1629_;
v___y_1588_ = v___y_1630_;
v___y_1589_ = v___y_1632_;
v___y_1590_ = v___y_1634_;
v___y_1591_ = v___y_1633_;
v___y_1592_ = v___y_1635_;
v___y_1593_ = v___y_1636_;
v___y_1594_ = v___y_1638_;
v___y_1595_ = v___y_1637_;
v___y_1596_ = v___y_1639_;
v___y_1597_ = v___y_1640_;
v___y_1598_ = v___y_1641_;
v___y_1599_ = v___x_1669_;
v___y_1600_ = v___y_1643_;
v___y_1601_ = v___y_1642_;
v___y_1602_ = v___y_1645_;
v___y_1603_ = v___y_1646_;
v___y_1604_ = v___y_1647_;
v___y_1605_ = v___y_1648_;
v___y_1606_ = v___y_1649_;
v___y_1607_ = v___x_1671_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1672_; 
lean_dec(v_doc_x3f_1352_);
v___x_1672_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___y_1573_ = v___y_1614_;
v___y_1574_ = v___y_1616_;
v___y_1575_ = v___y_1615_;
v___y_1576_ = v___y_1617_;
v___y_1577_ = v___y_1618_;
v___y_1578_ = v___y_1621_;
v___y_1579_ = v___y_1622_;
v___y_1580_ = v___y_1623_;
v___y_1581_ = v___x_1667_;
v___y_1582_ = v___y_1624_;
v___y_1583_ = v___y_1625_;
v___y_1584_ = v___y_1626_;
v___y_1585_ = v___x_1665_;
v___y_1586_ = v___y_1628_;
v___y_1587_ = v___y_1629_;
v___y_1588_ = v___y_1630_;
v___y_1589_ = v___y_1632_;
v___y_1590_ = v___y_1634_;
v___y_1591_ = v___y_1633_;
v___y_1592_ = v___y_1635_;
v___y_1593_ = v___y_1636_;
v___y_1594_ = v___y_1638_;
v___y_1595_ = v___y_1637_;
v___y_1596_ = v___y_1639_;
v___y_1597_ = v___y_1640_;
v___y_1598_ = v___y_1641_;
v___y_1599_ = v___x_1669_;
v___y_1600_ = v___y_1643_;
v___y_1601_ = v___y_1642_;
v___y_1602_ = v___y_1645_;
v___y_1603_ = v___y_1646_;
v___y_1604_ = v___y_1647_;
v___y_1605_ = v___y_1648_;
v___y_1606_ = v___y_1649_;
v___y_1607_ = v___x_1672_;
goto v___jp_1572_;
}
}
v___jp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74));
v___x_1677_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75);
lean_inc_ref(v_a_1359_);
v___x_1678_ = lean_apply_3(v_mkLogExceptionsTerm_1351_, v___x_1677_, v_a_1359_, v_a_1675_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1776_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_a_1680_ = lean_ctor_get(v___x_1678_, 1);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1682_ = v___x_1678_;
v_isShared_1683_ = v_isSharedCheck_1776_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1776_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_quotContext_1684_; lean_object* v_currMacroScope_1685_; lean_object* v_ref_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v_quotContext_1684_ = lean_ctor_get(v_a_1359_, 1);
v_currMacroScope_1685_ = lean_ctor_get(v_a_1359_, 2);
v_ref_1686_ = lean_ctor_get(v_a_1359_, 5);
v___x_1687_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78);
v___x_1688_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81);
v___x_1689_ = 0;
v___x_1690_ = l_Lean_SourceInfo_fromRef(v_ref_1686_, v___x_1689_);
v___x_1691_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83));
v___x_1692_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85);
v___x_1693_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86));
v___x_1694_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88));
lean_inc_n(v_currMacroScope_1685_, 2);
lean_inc_n(v_quotContext_1684_, 2);
v___x_1695_ = l_Lean_addMacroScope(v_quotContext_1684_, v___x_1694_, v_currMacroScope_1685_);
v___x_1696_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5));
v___x_1697_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6));
v___x_1698_ = lean_box(0);
v___x_1699_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91));
lean_inc_n(v___x_1690_, 3);
v___x_1700_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1690_);
lean_ctor_set(v___x_1700_, 1, v___x_1692_);
lean_ctor_set(v___x_1700_, 2, v___x_1695_);
lean_ctor_set(v___x_1700_, 3, v___x_1699_);
v___x_1701_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5));
v___x_1702_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93);
v___x_1703_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94));
v___x_1704_ = l_Lean_addMacroScope(v_quotContext_1684_, v___x_1703_, v_currMacroScope_1685_);
lean_inc(v___x_1704_);
v___x_1705_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1690_);
lean_ctor_set(v___x_1705_, 1, v___x_1702_);
lean_ctor_set(v___x_1705_, 2, v___x_1704_);
lean_ctor_set(v___x_1705_, 3, v___x_1698_);
v___x_1706_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96));
v___x_1707_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97));
if (v_isShared_1683_ == 0)
{
lean_ctor_set_tag(v___x_1682_, 2);
lean_ctor_set(v___x_1682_, 1, v___x_1707_);
lean_ctor_set(v___x_1682_, 0, v___x_1690_);
v___x_1709_ = v___x_1682_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1710_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99);
v___x_1711_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100));
lean_inc_n(v_currMacroScope_1685_, 2);
lean_inc_n(v_quotContext_1684_, 2);
v___x_1712_ = l_Lean_addMacroScope(v_quotContext_1684_, v___x_1711_, v_currMacroScope_1685_);
lean_inc(v___x_1712_);
lean_inc_n(v___x_1690_, 7);
v___x_1713_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1690_);
lean_ctor_set(v___x_1713_, 1, v___x_1710_);
lean_ctor_set(v___x_1713_, 2, v___x_1712_);
lean_ctor_set(v___x_1713_, 3, v___x_1698_);
v___x_1714_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101));
v___x_1715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1690_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102));
v___x_1717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1690_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
lean_inc_ref(v___x_1717_);
lean_inc_ref(v___x_1715_);
lean_inc_ref(v___x_1713_);
lean_inc_ref(v___x_1709_);
v___x_1718_ = l_Lean_Syntax_node5(v___x_1690_, v___x_1706_, v___x_1709_, v___x_1713_, v___x_1715_, v___x_1713_, v___x_1717_);
v___x_1719_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103);
v___x_1720_ = l_Lean_addMacroScope(v_quotContext_1684_, v___x_1676_, v_currMacroScope_1685_);
v___x_1721_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1690_);
lean_ctor_set(v___x_1721_, 1, v___x_1719_);
lean_ctor_set(v___x_1721_, 2, v___x_1720_);
lean_ctor_set(v___x_1721_, 3, v___x_1698_);
v___x_1722_ = l_Lean_Syntax_node5(v___x_1690_, v___x_1706_, v___x_1709_, v___x_1721_, v___x_1715_, v_a_1679_, v___x_1717_);
v___x_1723_ = l_Lean_Syntax_node5(v___x_1690_, v___x_1701_, v___x_1705_, v___x_1688_, v___x_1687_, v___x_1718_, v___x_1722_);
v___x_1724_ = l_Lean_Syntax_node2(v___x_1690_, v___x_1691_, v___x_1700_, v___x_1723_);
lean_inc_ref(v_a_1359_);
v___x_1725_ = lean_apply_3(v_mkMonadAdapt_1349_, v___x_1724_, v_a_1359_, v_a_1680_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1774_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
v_a_1727_ = lean_ctor_get(v___x_1725_, 1);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1729_ = v___x_1725_;
v_isShared_1730_ = v_isSharedCheck_1774_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_inc(v_a_1726_);
lean_dec(v___x_1725_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1774_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v_fnName_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v_ref_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1731_ = l_Lean_TSyntax_getId(v_elabName_1355_);
v___x_1732_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105));
v___x_1733_ = l_Lean_Name_append(v___x_1731_, v___x_1732_);
v_fnName_1734_ = l_Lean_mkIdentFrom(v_elabName_1355_, v___x_1733_, v___x_1689_);
v___x_1735_ = lean_unsigned_to_nat(3u);
v___x_1736_ = lean_mk_empty_array_with_capacity(v___x_1735_);
v___x_1737_ = lean_array_push(v___x_1736_, v_tk_1354_);
lean_inc(v_elabName_1355_);
v___x_1738_ = lean_array_push(v___x_1737_, v_elabName_1355_);
lean_inc(v_type_1356_);
v___x_1739_ = lean_array_push(v___x_1738_, v_type_1356_);
v___x_1740_ = lean_box(2);
v___x_1741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
lean_ctor_set(v___x_1741_, 1, v___x_1701_);
lean_ctor_set(v___x_1741_, 2, v___x_1739_);
v_ref_1742_ = l_Lean_replaceRef(v___x_1741_, v_ref_1686_);
lean_dec_ref_known(v___x_1741_, 3);
v___x_1743_ = l_Lean_SourceInfo_fromRef(v_ref_1742_, v___x_1689_);
lean_dec(v_ref_1742_);
v___x_1744_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1));
v___x_1745_ = lean_obj_once(&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6, &l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6_once, _init_l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6);
lean_inc_n(v___x_1743_, 2);
v___x_1746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1743_);
lean_ctor_set(v___x_1746_, 1, v___x_1701_);
lean_ctor_set(v___x_1746_, 2, v___x_1745_);
v___x_1747_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2));
v___x_1748_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106));
v___x_1749_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107));
if (v_isShared_1730_ == 0)
{
lean_ctor_set_tag(v___x_1729_, 2);
lean_ctor_set(v___x_1729_, 1, v___x_1748_);
lean_ctor_set(v___x_1729_, 0, v___x_1743_);
v___x_1751_ = v___x_1729_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v___x_1748_);
v___x_1751_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; size_t v_sz_1763_; size_t v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_inc_n(v___x_1743_, 9);
v___x_1752_ = l_Lean_Syntax_node1(v___x_1743_, v___x_1749_, v___x_1751_);
v___x_1753_ = l_Lean_Syntax_node1(v___x_1743_, v___x_1701_, v___x_1752_);
v___x_1754_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
v___x_1755_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108));
v___x_1756_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109));
v___x_1757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1743_);
lean_ctor_set(v___x_1757_, 1, v___x_1755_);
v___x_1758_ = l_Lean_Syntax_node1(v___x_1743_, v___x_1756_, v___x_1757_);
v___x_1759_ = l_Lean_Syntax_node1(v___x_1743_, v___x_1701_, v___x_1758_);
v___x_1760_ = l_Lean_Syntax_node1(v___x_1743_, v___x_1754_, v___x_1759_);
v___x_1761_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110));
v___x_1762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1743_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v_sz_1763_ = lean_array_size(v_binders_1357_);
v___x_1764_ = ((size_t)0ULL);
lean_inc_ref(v_binders_1357_);
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_1763_, v___x_1764_, v_binders_1357_);
v___x_1766_ = l_Array_append___redArg(v___x_1745_, v___x_1765_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1743_);
lean_ctor_set(v___x_1767_, 1, v___x_1701_);
lean_ctor_set(v___x_1767_, 2, v___x_1766_);
v___x_1768_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__111));
v___x_1769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1743_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
if (lean_obj_tag(v_entries_x3f_1358_) == 1)
{
lean_object* v_val_1770_; lean_object* v___x_1771_; 
v_val_1770_ = lean_ctor_get(v_entries_x3f_1358_, 0);
lean_inc(v_val_1770_);
lean_dec_ref_known(v_entries_x3f_1358_, 1);
v___x_1771_ = l_Array_mkArray1___redArg(v_val_1770_);
lean_inc(v_quotContext_1684_);
lean_inc(v_currMacroScope_1685_);
v___y_1614_ = v___x_1743_;
v___y_1615_ = v___x_1712_;
v___y_1616_ = v___x_1746_;
v___y_1617_ = v_a_1727_;
v___y_1618_ = v_currMacroScope_1685_;
v___y_1619_ = v___x_1744_;
v___y_1620_ = v___x_1762_;
v___y_1621_ = v___x_1704_;
v___y_1622_ = v___x_1691_;
v___y_1623_ = v___x_1687_;
v___y_1624_ = v___x_1747_;
v___y_1625_ = v___x_1697_;
v___y_1626_ = v___x_1714_;
v___y_1627_ = v___x_1760_;
v___y_1628_ = v_sz_1763_;
v___y_1629_ = v___x_1702_;
v___y_1630_ = v___x_1693_;
v___y_1631_ = v___x_1769_;
v___y_1632_ = v___x_1716_;
v___y_1633_ = v_a_1674_;
v___y_1634_ = v___x_1710_;
v___y_1635_ = v_fnName_1734_;
v___y_1636_ = v___x_1707_;
v___y_1637_ = v___x_1698_;
v___y_1638_ = v___x_1740_;
v___y_1639_ = v_quotContext_1684_;
v___y_1640_ = v___x_1706_;
v___y_1641_ = v_a_1726_;
v___y_1642_ = v___x_1764_;
v___y_1643_ = v___x_1688_;
v___y_1644_ = v___x_1767_;
v___y_1645_ = v___x_1701_;
v___y_1646_ = v___x_1698_;
v___y_1647_ = v___x_1677_;
v___y_1648_ = v___x_1696_;
v___y_1649_ = v___x_1745_;
v___y_1650_ = v___x_1753_;
v___y_1651_ = v___x_1771_;
goto v___jp_1613_;
}
else
{
lean_object* v___x_1772_; 
lean_dec(v_entries_x3f_1358_);
v___x_1772_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
lean_inc(v_quotContext_1684_);
lean_inc(v_currMacroScope_1685_);
v___y_1614_ = v___x_1743_;
v___y_1615_ = v___x_1712_;
v___y_1616_ = v___x_1746_;
v___y_1617_ = v_a_1727_;
v___y_1618_ = v_currMacroScope_1685_;
v___y_1619_ = v___x_1744_;
v___y_1620_ = v___x_1762_;
v___y_1621_ = v___x_1704_;
v___y_1622_ = v___x_1691_;
v___y_1623_ = v___x_1687_;
v___y_1624_ = v___x_1747_;
v___y_1625_ = v___x_1697_;
v___y_1626_ = v___x_1714_;
v___y_1627_ = v___x_1760_;
v___y_1628_ = v_sz_1763_;
v___y_1629_ = v___x_1702_;
v___y_1630_ = v___x_1693_;
v___y_1631_ = v___x_1769_;
v___y_1632_ = v___x_1716_;
v___y_1633_ = v_a_1674_;
v___y_1634_ = v___x_1710_;
v___y_1635_ = v_fnName_1734_;
v___y_1636_ = v___x_1707_;
v___y_1637_ = v___x_1698_;
v___y_1638_ = v___x_1740_;
v___y_1639_ = v_quotContext_1684_;
v___y_1640_ = v___x_1706_;
v___y_1641_ = v_a_1726_;
v___y_1642_ = v___x_1764_;
v___y_1643_ = v___x_1688_;
v___y_1644_ = v___x_1767_;
v___y_1645_ = v___x_1701_;
v___y_1646_ = v___x_1698_;
v___y_1647_ = v___x_1677_;
v___y_1648_ = v___x_1696_;
v___y_1649_ = v___x_1745_;
v___y_1650_ = v___x_1753_;
v___y_1651_ = v___x_1772_;
goto v___jp_1613_;
}
}
}
}
else
{
lean_dec(v___x_1712_);
lean_dec(v___x_1704_);
lean_dec_ref(v_a_1674_);
lean_dec(v_entries_x3f_1358_);
lean_dec_ref(v_binders_1357_);
lean_dec(v_type_1356_);
lean_dec(v_elabName_1355_);
lean_dec(v_tk_1354_);
lean_dec(v_vis_x3f_1353_);
lean_dec(v_doc_x3f_1352_);
lean_dec(v_logExceptionsDefault_1350_);
lean_dec(v_monad_1348_);
return v___x_1725_;
}
}
}
}
else
{
lean_dec_ref(v_a_1674_);
lean_dec(v_entries_x3f_1358_);
lean_dec_ref(v_binders_1357_);
lean_dec(v_type_1356_);
lean_dec(v_elabName_1355_);
lean_dec(v_tk_1354_);
lean_dec(v_vis_x3f_1353_);
lean_dec(v_doc_x3f_1352_);
lean_dec(v_logExceptionsDefault_1350_);
lean_dec_ref(v_mkMonadAdapt_1349_);
lean_dec(v_monad_1348_);
return v___x_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___boxed(lean_object* v_monad_1793_, lean_object* v_mkMonadAdapt_1794_, lean_object* v_logExceptionsDefault_1795_, lean_object* v_mkLogExceptionsTerm_1796_, lean_object* v_doc_x3f_1797_, lean_object* v_vis_x3f_1798_, lean_object* v_tk_1799_, lean_object* v_elabName_1800_, lean_object* v_type_1801_, lean_object* v_binders_1802_, lean_object* v_entries_x3f_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v_monad_1793_, v_mkMonadAdapt_1794_, v_logExceptionsDefault_1795_, v_mkLogExceptionsTerm_1796_, v_doc_x3f_1797_, v_vis_x3f_1798_, v_tk_1799_, v_elabName_1800_, v_type_1801_, v_binders_1802_, v_entries_x3f_1803_, v_a_1804_, v_a_1805_);
lean_dec_ref(v_a_1804_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0(lean_object* v_logExceptions_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v_logExceptions_1807_);
lean_ctor_set(v___x_1810_, 1, v___y_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0___boxed(lean_object* v_logExceptions_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0(v_logExceptions_1811_, v___y_1812_, v___y_1813_);
lean_dec_ref(v___y_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1(lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___y_1815_);
lean_ctor_set(v___x_1818_, 1, v___y_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1___boxed(lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1(v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1822_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6));
v___x_1838_ = l_Lean_mkCIdent(v___x_1837_);
return v___x_1838_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9));
v___x_1844_ = l_Lean_mkCIdent(v___x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab(lean_object* v_x_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1));
lean_inc(v_x_1845_);
v___x_1849_ = l_Lean_Syntax_isOfKind(v_x_1845_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; 
lean_dec(v_x_1845_);
v___x_1850_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1847_);
return v___x_1850_;
}
else
{
lean_object* v___f_1851_; lean_object* v___f_1852_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v_entries_x3f_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___x_1885_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v_vis_x3f_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v_doc_x3f_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___f_1851_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2));
v___f_1852_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3));
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1928_ = l_Lean_Syntax_getArg(v_x_1845_, v___x_1885_);
v___x_1929_ = l_Lean_Syntax_isNone(v___x_1928_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1930_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1928_);
v___x_1931_ = l_Lean_Syntax_matchesNull(v___x_1928_, v___x_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; 
lean_dec(v___x_1928_);
lean_dec(v_x_1845_);
v___x_1932_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1847_);
return v___x_1932_;
}
else
{
lean_object* v_doc_x3f_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v_doc_x3f_1933_ = l_Lean_Syntax_getArg(v___x_1928_, v___x_1885_);
lean_dec(v___x_1928_);
v___x_1934_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_1933_);
v___x_1935_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; 
lean_dec(v_doc_x3f_1933_);
lean_dec(v_x_1845_);
v___x_1936_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1847_);
return v___x_1936_;
}
else
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1937_, 0, v_doc_x3f_1933_);
v_doc_x3f_1917_ = v___x_1937_;
v___y_1918_ = v_a_1846_;
v___y_1919_ = v_a_1847_;
goto v___jp_1916_;
}
}
}
else
{
lean_object* v___x_1938_; 
lean_dec(v___x_1928_);
v___x_1938_ = lean_box(0);
v_doc_x3f_1917_ = v___x_1938_;
v___y_1918_ = v_a_1846_;
v___y_1919_ = v_a_1847_;
goto v___jp_1916_;
}
v___jp_1853_:
{
lean_object* v_binders_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_binders_1863_ = l_Lean_Syntax_getArgs(v___y_1857_);
lean_dec(v___y_1857_);
v___x_1864_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7, &l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7_once, _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7);
v___x_1865_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10, &l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10_once, _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10);
v___x_1866_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_1864_, v___f_1852_, v___x_1865_, v___f_1851_, v___y_1858_, v___y_1859_, v___y_1854_, v___y_1856_, v___y_1855_, v_binders_1863_, v_entries_x3f_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_a_1868_ = lean_ctor_get(v___x_1866_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1866_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1867_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_a_1876_ = lean_ctor_get(v___x_1866_, 0);
v_a_1877_ = lean_ctor_get(v___x_1866_, 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1866_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_inc(v_a_1876_);
lean_dec(v___x_1866_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1876_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
v___jp_1886_:
{
lean_object* v___x_1892_; lean_object* v_elabName_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1892_ = lean_unsigned_to_nat(3u);
v_elabName_1893_ = l_Lean_Syntax_getArg(v_x_1845_, v___x_1892_);
v___x_1894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_elabName_1893_);
v___x_1895_ = l_Lean_Syntax_isOfKind(v_elabName_1893_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; 
lean_dec(v_elabName_1893_);
lean_dec(v_vis_x3f_1889_);
lean_dec(v___y_1888_);
lean_dec(v_x_1845_);
v___x_1896_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1891_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; lean_object* v_type_1898_; uint8_t v___x_1899_; 
v___x_1897_ = lean_unsigned_to_nat(4u);
v_type_1898_ = l_Lean_Syntax_getArg(v_x_1845_, v___x_1897_);
lean_inc(v_type_1898_);
v___x_1899_ = l_Lean_Syntax_isOfKind(v_type_1898_, v___x_1894_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; 
lean_dec(v_type_1898_);
lean_dec(v_elabName_1893_);
lean_dec(v_vis_x3f_1889_);
lean_dec(v___y_1888_);
lean_dec(v_x_1845_);
v___x_1900_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1891_);
return v___x_1900_;
}
else
{
lean_object* v___x_1901_; lean_object* v_tk_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1901_ = lean_unsigned_to_nat(2u);
v_tk_1902_ = l_Lean_Syntax_getArg(v_x_1845_, v___x_1901_);
v___x_1903_ = lean_unsigned_to_nat(5u);
v___x_1904_ = l_Lean_Syntax_getArg(v_x_1845_, v___x_1903_);
v___x_1905_ = lean_unsigned_to_nat(6u);
v___x_1906_ = l_Lean_Syntax_getArg(v_x_1845_, v___x_1905_);
lean_dec(v_x_1845_);
v___x_1907_ = l_Lean_Syntax_isNone(v___x_1906_);
if (v___x_1907_ == 0)
{
uint8_t v___x_1908_; 
lean_inc(v___x_1906_);
v___x_1908_ = l_Lean_Syntax_matchesNull(v___x_1906_, v___y_1887_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; 
lean_dec(v___x_1906_);
lean_dec(v___x_1904_);
lean_dec(v_tk_1902_);
lean_dec(v_type_1898_);
lean_dec(v_elabName_1893_);
lean_dec(v_vis_x3f_1889_);
lean_dec(v___y_1888_);
v___x_1909_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1891_);
return v___x_1909_;
}
else
{
lean_object* v_entries_x3f_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v_entries_x3f_1910_ = l_Lean_Syntax_getArg(v___x_1906_, v___x_1885_);
lean_dec(v___x_1906_);
v___x_1911_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_1910_);
v___x_1912_ = l_Lean_Syntax_isOfKind(v_entries_x3f_1910_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
lean_dec(v_entries_x3f_1910_);
lean_dec(v___x_1904_);
lean_dec(v_tk_1902_);
lean_dec(v_type_1898_);
lean_dec(v_elabName_1893_);
lean_dec(v_vis_x3f_1889_);
lean_dec(v___y_1888_);
v___x_1913_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1891_);
return v___x_1913_;
}
else
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_entries_x3f_1910_);
v___y_1854_ = v_tk_1902_;
v___y_1855_ = v_type_1898_;
v___y_1856_ = v_elabName_1893_;
v___y_1857_ = v___x_1904_;
v___y_1858_ = v___y_1888_;
v___y_1859_ = v_vis_x3f_1889_;
v_entries_x3f_1860_ = v___x_1914_;
v___y_1861_ = v___y_1890_;
v___y_1862_ = v___y_1891_;
goto v___jp_1853_;
}
}
}
else
{
lean_object* v___x_1915_; 
lean_dec(v___x_1906_);
v___x_1915_ = lean_box(0);
v___y_1854_ = v_tk_1902_;
v___y_1855_ = v_type_1898_;
v___y_1856_ = v_elabName_1893_;
v___y_1857_ = v___x_1904_;
v___y_1858_ = v___y_1888_;
v___y_1859_ = v_vis_x3f_1889_;
v_entries_x3f_1860_ = v___x_1915_;
v___y_1861_ = v___y_1890_;
v___y_1862_ = v___y_1891_;
goto v___jp_1853_;
}
}
}
}
v___jp_1916_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1920_ = lean_unsigned_to_nat(1u);
v___x_1921_ = l_Lean_Syntax_getArg(v_x_1845_, v___x_1920_);
v___x_1922_ = l_Lean_Syntax_isNone(v___x_1921_);
if (v___x_1922_ == 0)
{
uint8_t v___x_1923_; 
lean_inc(v___x_1921_);
v___x_1923_ = l_Lean_Syntax_matchesNull(v___x_1921_, v___x_1920_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; 
lean_dec(v___x_1921_);
lean_dec(v_doc_x3f_1917_);
lean_dec(v_x_1845_);
v___x_1924_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1919_);
return v___x_1924_;
}
else
{
lean_object* v_vis_x3f_1925_; lean_object* v___x_1926_; 
v_vis_x3f_1925_ = l_Lean_Syntax_getArg(v___x_1921_, v___x_1885_);
lean_dec(v___x_1921_);
v___x_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_vis_x3f_1925_);
v___y_1887_ = v___x_1920_;
v___y_1888_ = v_doc_x3f_1917_;
v_vis_x3f_1889_ = v___x_1926_;
v___y_1890_ = v___y_1918_;
v___y_1891_ = v___y_1919_;
goto v___jp_1886_;
}
}
else
{
lean_object* v___x_1927_; 
lean_dec(v___x_1921_);
v___x_1927_ = lean_box(0);
v___y_1887_ = v___x_1920_;
v___y_1888_ = v_doc_x3f_1917_;
v_vis_x3f_1889_ = v___x_1927_;
v___y_1890_ = v___y_1918_;
v___y_1891_ = v___y_1919_;
goto v___jp_1886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___boxed(lean_object* v_x_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab(v_x_1939_, v_a_1940_, v_a_1941_);
lean_dec_ref(v_a_1940_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1(){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1950_ = l_Lean_Elab_macroAttribute;
v___x_1951_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1));
v___x_1952_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1));
v___x_1953_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___boxed), 3, 0);
v___x_1954_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1950_, v___x_1951_, v___x_1952_, v___x_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___boxed(lean_object* v_a_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1();
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab(lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1961_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_1962_ = lean_unsigned_to_nat(2u);
v___x_1963_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_1961_, v___x_1962_, v_a_1957_, v_a_1958_, v_a_1959_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___boxed(lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab(v_a_1964_, v_a_1965_, v_a_1966_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
lean_dec(v_a_1964_);
return v_res_1968_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___boxed), 4, 0);
v___x_1970_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_1970_, 0, v___x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1(){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1));
v___x_1973_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0);
v___x_1974_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_1972_, v___x_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___boxed(lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1();
return v_res_1976_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__8));
v___x_1989_ = l_String_toRawSubstring_x27(v___x_1988_);
return v___x_1989_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13));
v___x_1995_ = l_String_toRawSubstring_x27(v___x_1994_);
return v___x_1995_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__21));
v___x_2011_ = l_String_toRawSubstring_x27(v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1(lean_object* v___x_2014_, lean_object* v___x_2015_, lean_object* v___x_2016_, lean_object* v___x_2017_, lean_object* v___x_2018_, lean_object* v_logExceptions_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_quotContext_2022_; lean_object* v_currMacroScope_2023_; lean_object* v_ref_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_quotContext_2022_ = lean_ctor_get(v___y_2020_, 1);
v_currMacroScope_2023_ = lean_ctor_get(v___y_2020_, 2);
v_ref_2024_ = lean_ctor_get(v___y_2020_, 5);
v___x_2025_ = 0;
v___x_2026_ = l_Lean_SourceInfo_fromRef(v_ref_2024_, v___x_2025_);
v___x_2027_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1));
v___x_2028_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2));
lean_inc_n(v___x_2026_, 14);
v___x_2029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2026_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3));
lean_inc_ref_n(v___x_2016_, 5);
lean_inc_ref_n(v___x_2015_, 4);
lean_inc_ref_n(v___x_2014_, 9);
v___x_2031_ = l_Lean_Name_mkStr4(v___x_2014_, v___x_2015_, v___x_2016_, v___x_2030_);
v___x_2032_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4));
v___x_2033_ = l_Lean_Name_mkStr4(v___x_2014_, v___x_2015_, v___x_2016_, v___x_2032_);
v___x_2034_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5));
v___x_2035_ = l_Lean_Name_mkStr4(v___x_2014_, v___x_2015_, v___x_2016_, v___x_2034_);
v___x_2036_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97));
v___x_2037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2026_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7));
v___x_2039_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9);
v___x_2040_ = lean_box(0);
lean_inc_n(v_currMacroScope_2023_, 3);
lean_inc_n(v_quotContext_2022_, 3);
v___x_2041_ = l_Lean_addMacroScope(v_quotContext_2022_, v___x_2040_, v_currMacroScope_2023_);
lean_inc_ref_n(v___x_2017_, 2);
v___x_2042_ = l_Lean_Name_mkStr3(v___x_2014_, v___x_2017_, v___x_2018_);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
v___x_2044_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10));
v___x_2045_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2));
v___x_2046_ = l_Lean_Name_mkStr3(v___x_2014_, v___x_2044_, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
v___x_2048_ = l_Lean_Name_mkStr3(v___x_2014_, v___x_2017_, v___x_2045_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
v___x_2050_ = l_Lean_Name_mkStr3(v___x_2014_, v___x_2017_, v___x_2016_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
v___x_2052_ = l_Lean_Name_mkStr2(v___x_2014_, v___x_2044_);
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
v___x_2054_ = lean_box(0);
v___x_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2053_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2051_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2049_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2047_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
v___x_2059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2043_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2026_);
lean_ctor_set(v___x_2060_, 1, v___x_2039_);
lean_ctor_set(v___x_2060_, 2, v___x_2041_);
lean_ctor_set(v___x_2060_, 3, v___x_2059_);
v___x_2061_ = l_Lean_Syntax_node1(v___x_2026_, v___x_2038_, v___x_2060_);
v___x_2062_ = l_Lean_Syntax_node2(v___x_2026_, v___x_2035_, v___x_2037_, v___x_2061_);
v___x_2063_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11));
v___x_2064_ = l_Lean_Name_mkStr4(v___x_2014_, v___x_2015_, v___x_2016_, v___x_2063_);
v___x_2065_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12));
v___x_2066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2026_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66));
v___x_2068_ = l_Lean_Name_mkStr4(v___x_2014_, v___x_2015_, v___x_2016_, v___x_2067_);
v___x_2069_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14);
v___x_2070_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15));
v___x_2071_ = l_Lean_addMacroScope(v_quotContext_2022_, v___x_2070_, v_currMacroScope_2023_);
v___x_2072_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19));
v___x_2073_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2026_);
lean_ctor_set(v___x_2073_, 1, v___x_2069_);
lean_ctor_set(v___x_2073_, 2, v___x_2071_);
lean_ctor_set(v___x_2073_, 3, v___x_2072_);
v___x_2074_ = l_Lean_Syntax_node1(v___x_2026_, v___x_2068_, v___x_2073_);
v___x_2075_ = l_Lean_Syntax_node2(v___x_2026_, v___x_2064_, v___x_2066_, v___x_2074_);
v___x_2076_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102));
v___x_2077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2026_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = l_Lean_Syntax_node3(v___x_2026_, v___x_2033_, v___x_2062_, v___x_2075_, v___x_2077_);
v___x_2079_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20));
v___x_2080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2026_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
v___x_2081_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22);
v___x_2082_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__23));
v___x_2083_ = l_Lean_addMacroScope(v_quotContext_2022_, v___x_2082_, v_currMacroScope_2023_);
v___x_2084_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2026_);
lean_ctor_set(v___x_2084_, 1, v___x_2081_);
lean_ctor_set(v___x_2084_, 2, v___x_2083_);
lean_ctor_set(v___x_2084_, 3, v___x_2054_);
v___x_2085_ = l_Lean_Syntax_node3(v___x_2026_, v___x_2031_, v___x_2078_, v___x_2080_, v___x_2084_);
v___x_2086_ = l_Lean_Syntax_node3(v___x_2026_, v___x_2027_, v_logExceptions_2019_, v___x_2029_, v___x_2085_);
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v___y_2021_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___boxed(lean_object* v___x_2088_, lean_object* v___x_2089_, lean_object* v___x_2090_, lean_object* v___x_2091_, lean_object* v___x_2092_, lean_object* v_logExceptions_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1(v___x_2088_, v___x_2089_, v___x_2090_, v___x_2091_, v___x_2092_, v_logExceptions_2093_, v___y_2094_, v___y_2095_);
lean_dec_ref(v___y_2094_);
return v_res_2096_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4));
v___x_2116_ = l_Lean_mkCIdent(v___x_2115_);
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7));
v___x_2122_ = l_Lean_mkCIdent(v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab(lean_object* v_x_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1));
lean_inc(v_x_2123_);
v___x_2127_ = l_Lean_Syntax_isOfKind(v_x_2123_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; 
lean_dec(v_x_2123_);
v___x_2128_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2125_);
return v___x_2128_;
}
else
{
lean_object* v___f_2129_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v_entries_x3f_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___x_2163_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v_vis_x3f_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v_doc_x3f_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___f_2129_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3));
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2206_ = l_Lean_Syntax_getArg(v_x_2123_, v___x_2163_);
v___x_2207_ = l_Lean_Syntax_isNone(v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; uint8_t v___x_2209_; 
v___x_2208_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2206_);
v___x_2209_ = l_Lean_Syntax_matchesNull(v___x_2206_, v___x_2208_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; 
lean_dec(v___x_2206_);
lean_dec(v_x_2123_);
v___x_2210_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2125_);
return v___x_2210_;
}
else
{
lean_object* v_doc_x3f_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v_doc_x3f_2211_ = l_Lean_Syntax_getArg(v___x_2206_, v___x_2163_);
lean_dec(v___x_2206_);
v___x_2212_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_2211_);
v___x_2213_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2211_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
lean_dec(v_doc_x3f_2211_);
lean_dec(v_x_2123_);
v___x_2214_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2125_);
return v___x_2214_;
}
else
{
lean_object* v___x_2215_; 
v___x_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2215_, 0, v_doc_x3f_2211_);
v_doc_x3f_2195_ = v___x_2215_;
v___y_2196_ = v_a_2124_;
v___y_2197_ = v_a_2125_;
goto v___jp_2194_;
}
}
}
else
{
lean_object* v___x_2216_; 
lean_dec(v___x_2206_);
v___x_2216_ = lean_box(0);
v_doc_x3f_2195_ = v___x_2216_;
v___y_2196_ = v_a_2124_;
v___y_2197_ = v_a_2125_;
goto v___jp_2194_;
}
v___jp_2130_:
{
lean_object* v___f_2140_; lean_object* v_binders_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___f_2140_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2));
v_binders_2141_ = l_Lean_Syntax_getArgs(v___y_2134_);
lean_dec(v___y_2134_);
v___x_2142_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5);
v___x_2143_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8);
v___x_2144_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_2142_, v___f_2129_, v___x_2143_, v___f_2140_, v___y_2131_, v___y_2136_, v___y_2132_, v___y_2133_, v___y_2135_, v_binders_2141_, v_entries_x3f_2137_, v___y_2138_, v___y_2139_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_a_2146_ = lean_ctor_get(v___x_2144_, 1);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2144_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2145_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
v_a_2154_ = lean_ctor_get(v___x_2144_, 0);
v_a_2155_ = lean_ctor_get(v___x_2144_, 1);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2144_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_inc(v_a_2154_);
lean_dec(v___x_2144_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2154_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
v___jp_2164_:
{
lean_object* v___x_2170_; lean_object* v_elabName_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2170_ = lean_unsigned_to_nat(3u);
v_elabName_2171_ = l_Lean_Syntax_getArg(v_x_2123_, v___x_2170_);
v___x_2172_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_elabName_2171_);
v___x_2173_ = l_Lean_Syntax_isOfKind(v_elabName_2171_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
lean_dec(v_elabName_2171_);
lean_dec(v_vis_x3f_2167_);
lean_dec(v___y_2165_);
lean_dec(v_x_2123_);
v___x_2174_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2169_);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; lean_object* v_type_2176_; uint8_t v___x_2177_; 
v___x_2175_ = lean_unsigned_to_nat(4u);
v_type_2176_ = l_Lean_Syntax_getArg(v_x_2123_, v___x_2175_);
lean_inc(v_type_2176_);
v___x_2177_ = l_Lean_Syntax_isOfKind(v_type_2176_, v___x_2172_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; 
lean_dec(v_type_2176_);
lean_dec(v_elabName_2171_);
lean_dec(v_vis_x3f_2167_);
lean_dec(v___y_2165_);
lean_dec(v_x_2123_);
v___x_2178_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2169_);
return v___x_2178_;
}
else
{
lean_object* v___x_2179_; lean_object* v_tk_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2179_ = lean_unsigned_to_nat(2u);
v_tk_2180_ = l_Lean_Syntax_getArg(v_x_2123_, v___x_2179_);
v___x_2181_ = lean_unsigned_to_nat(5u);
v___x_2182_ = l_Lean_Syntax_getArg(v_x_2123_, v___x_2181_);
v___x_2183_ = lean_unsigned_to_nat(6u);
v___x_2184_ = l_Lean_Syntax_getArg(v_x_2123_, v___x_2183_);
lean_dec(v_x_2123_);
v___x_2185_ = l_Lean_Syntax_isNone(v___x_2184_);
if (v___x_2185_ == 0)
{
uint8_t v___x_2186_; 
lean_inc(v___x_2184_);
v___x_2186_ = l_Lean_Syntax_matchesNull(v___x_2184_, v___y_2166_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; 
lean_dec(v___x_2184_);
lean_dec(v___x_2182_);
lean_dec(v_tk_2180_);
lean_dec(v_type_2176_);
lean_dec(v_elabName_2171_);
lean_dec(v_vis_x3f_2167_);
lean_dec(v___y_2165_);
v___x_2187_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2169_);
return v___x_2187_;
}
else
{
lean_object* v_entries_x3f_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v_entries_x3f_2188_ = l_Lean_Syntax_getArg(v___x_2184_, v___x_2163_);
lean_dec(v___x_2184_);
v___x_2189_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_2188_);
v___x_2190_ = l_Lean_Syntax_isOfKind(v_entries_x3f_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
lean_dec(v_entries_x3f_2188_);
lean_dec(v___x_2182_);
lean_dec(v_tk_2180_);
lean_dec(v_type_2176_);
lean_dec(v_elabName_2171_);
lean_dec(v_vis_x3f_2167_);
lean_dec(v___y_2165_);
v___x_2191_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2169_);
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2192_, 0, v_entries_x3f_2188_);
v___y_2131_ = v___y_2165_;
v___y_2132_ = v_tk_2180_;
v___y_2133_ = v_elabName_2171_;
v___y_2134_ = v___x_2182_;
v___y_2135_ = v_type_2176_;
v___y_2136_ = v_vis_x3f_2167_;
v_entries_x3f_2137_ = v___x_2192_;
v___y_2138_ = v___y_2168_;
v___y_2139_ = v___y_2169_;
goto v___jp_2130_;
}
}
}
else
{
lean_object* v___x_2193_; 
lean_dec(v___x_2184_);
v___x_2193_ = lean_box(0);
v___y_2131_ = v___y_2165_;
v___y_2132_ = v_tk_2180_;
v___y_2133_ = v_elabName_2171_;
v___y_2134_ = v___x_2182_;
v___y_2135_ = v_type_2176_;
v___y_2136_ = v_vis_x3f_2167_;
v_entries_x3f_2137_ = v___x_2193_;
v___y_2138_ = v___y_2168_;
v___y_2139_ = v___y_2169_;
goto v___jp_2130_;
}
}
}
}
v___jp_2194_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2198_ = lean_unsigned_to_nat(1u);
v___x_2199_ = l_Lean_Syntax_getArg(v_x_2123_, v___x_2198_);
v___x_2200_ = l_Lean_Syntax_isNone(v___x_2199_);
if (v___x_2200_ == 0)
{
uint8_t v___x_2201_; 
lean_inc(v___x_2199_);
v___x_2201_ = l_Lean_Syntax_matchesNull(v___x_2199_, v___x_2198_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; 
lean_dec(v___x_2199_);
lean_dec(v_doc_x3f_2195_);
lean_dec(v_x_2123_);
v___x_2202_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2197_);
return v___x_2202_;
}
else
{
lean_object* v_vis_x3f_2203_; lean_object* v___x_2204_; 
v_vis_x3f_2203_ = l_Lean_Syntax_getArg(v___x_2199_, v___x_2163_);
lean_dec(v___x_2199_);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v_vis_x3f_2203_);
v___y_2165_ = v_doc_x3f_2195_;
v___y_2166_ = v___x_2198_;
v_vis_x3f_2167_ = v___x_2204_;
v___y_2168_ = v___y_2196_;
v___y_2169_ = v___y_2197_;
goto v___jp_2164_;
}
}
else
{
lean_object* v___x_2205_; 
lean_dec(v___x_2199_);
v___x_2205_ = lean_box(0);
v___y_2165_ = v_doc_x3f_2195_;
v___y_2166_ = v___x_2198_;
v_vis_x3f_2167_ = v___x_2205_;
v___y_2168_ = v___y_2196_;
v___y_2169_ = v___y_2197_;
goto v___jp_2164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___boxed(lean_object* v_x_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab(v_x_2217_, v_a_2218_, v_a_2219_);
lean_dec_ref(v_a_2218_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1(){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2228_ = l_Lean_Elab_macroAttribute;
v___x_2229_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1));
v___x_2230_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1));
v___x_2231_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___boxed), 3, 0);
v___x_2232_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2228_, v___x_2229_, v___x_2230_, v___x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___boxed(lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1();
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab(lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_2240_ = lean_unsigned_to_nat(2u);
v___x_2241_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_2239_, v___x_2240_, v_a_2235_, v_a_2236_, v_a_2237_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___boxed(lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab(v_a_2242_, v_a_2243_, v_a_2244_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
lean_dec(v_a_2242_);
return v_res_2246_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___boxed), 4, 0);
v___x_2248_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_2248_, 0, v___x_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1(){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1));
v___x_2251_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0);
v___x_2252_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_2250_, v___x_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___boxed(lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1();
return v_res_2254_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__0));
v___x_2257_ = l_String_toRawSubstring_x27(v___x_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1(lean_object* v___x_2260_, lean_object* v___x_2261_, lean_object* v___x_2262_, lean_object* v___x_2263_, lean_object* v___x_2264_, lean_object* v_logExceptions_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_quotContext_2268_; lean_object* v_currMacroScope_2269_; lean_object* v_ref_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v_quotContext_2268_ = lean_ctor_get(v___y_2266_, 1);
v_currMacroScope_2269_ = lean_ctor_get(v___y_2266_, 2);
v_ref_2270_ = lean_ctor_get(v___y_2266_, 5);
v___x_2271_ = 0;
v___x_2272_ = l_Lean_SourceInfo_fromRef(v_ref_2270_, v___x_2271_);
v___x_2273_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1));
v___x_2274_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2));
lean_inc_n(v___x_2272_, 14);
v___x_2275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2272_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3));
lean_inc_ref_n(v___x_2262_, 5);
lean_inc_ref_n(v___x_2261_, 4);
lean_inc_ref_n(v___x_2260_, 9);
v___x_2277_ = l_Lean_Name_mkStr4(v___x_2260_, v___x_2261_, v___x_2262_, v___x_2276_);
v___x_2278_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4));
v___x_2279_ = l_Lean_Name_mkStr4(v___x_2260_, v___x_2261_, v___x_2262_, v___x_2278_);
v___x_2280_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5));
v___x_2281_ = l_Lean_Name_mkStr4(v___x_2260_, v___x_2261_, v___x_2262_, v___x_2280_);
v___x_2282_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97));
v___x_2283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2272_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7));
v___x_2285_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9);
v___x_2286_ = lean_box(0);
lean_inc_n(v_currMacroScope_2269_, 3);
lean_inc_n(v_quotContext_2268_, 3);
v___x_2287_ = l_Lean_addMacroScope(v_quotContext_2268_, v___x_2286_, v_currMacroScope_2269_);
lean_inc_ref_n(v___x_2263_, 2);
v___x_2288_ = l_Lean_Name_mkStr3(v___x_2260_, v___x_2263_, v___x_2264_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
v___x_2290_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10));
v___x_2291_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2));
v___x_2292_ = l_Lean_Name_mkStr3(v___x_2260_, v___x_2290_, v___x_2291_);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
v___x_2294_ = l_Lean_Name_mkStr3(v___x_2260_, v___x_2263_, v___x_2291_);
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
v___x_2296_ = l_Lean_Name_mkStr3(v___x_2260_, v___x_2263_, v___x_2262_);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
v___x_2298_ = l_Lean_Name_mkStr2(v___x_2260_, v___x_2290_);
v___x_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
v___x_2300_ = lean_box(0);
v___x_2301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2297_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2295_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2293_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2289_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2272_);
lean_ctor_set(v___x_2306_, 1, v___x_2285_);
lean_ctor_set(v___x_2306_, 2, v___x_2287_);
lean_ctor_set(v___x_2306_, 3, v___x_2305_);
v___x_2307_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2284_, v___x_2306_);
v___x_2308_ = l_Lean_Syntax_node2(v___x_2272_, v___x_2281_, v___x_2283_, v___x_2307_);
v___x_2309_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11));
v___x_2310_ = l_Lean_Name_mkStr4(v___x_2260_, v___x_2261_, v___x_2262_, v___x_2309_);
v___x_2311_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12));
v___x_2312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2272_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66));
v___x_2314_ = l_Lean_Name_mkStr4(v___x_2260_, v___x_2261_, v___x_2262_, v___x_2313_);
v___x_2315_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14);
v___x_2316_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15));
v___x_2317_ = l_Lean_addMacroScope(v_quotContext_2268_, v___x_2316_, v_currMacroScope_2269_);
v___x_2318_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19));
v___x_2319_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2272_);
lean_ctor_set(v___x_2319_, 1, v___x_2315_);
lean_ctor_set(v___x_2319_, 2, v___x_2317_);
lean_ctor_set(v___x_2319_, 3, v___x_2318_);
v___x_2320_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2314_, v___x_2319_);
v___x_2321_ = l_Lean_Syntax_node2(v___x_2272_, v___x_2310_, v___x_2312_, v___x_2320_);
v___x_2322_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102));
v___x_2323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2272_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = l_Lean_Syntax_node3(v___x_2272_, v___x_2279_, v___x_2308_, v___x_2321_, v___x_2323_);
v___x_2325_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20));
v___x_2326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2272_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
v___x_2327_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1, &l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1);
v___x_2328_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__2));
v___x_2329_ = l_Lean_addMacroScope(v_quotContext_2268_, v___x_2328_, v_currMacroScope_2269_);
v___x_2330_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2272_);
lean_ctor_set(v___x_2330_, 1, v___x_2327_);
lean_ctor_set(v___x_2330_, 2, v___x_2329_);
lean_ctor_set(v___x_2330_, 3, v___x_2300_);
v___x_2331_ = l_Lean_Syntax_node3(v___x_2272_, v___x_2277_, v___x_2324_, v___x_2326_, v___x_2330_);
v___x_2332_ = l_Lean_Syntax_node3(v___x_2272_, v___x_2273_, v_logExceptions_2265_, v___x_2275_, v___x_2331_);
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set(v___x_2333_, 1, v___y_2267_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___boxed(lean_object* v___x_2334_, lean_object* v___x_2335_, lean_object* v___x_2336_, lean_object* v___x_2337_, lean_object* v___x_2338_, lean_object* v_logExceptions_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1(v___x_2334_, v___x_2335_, v___x_2336_, v___x_2337_, v___x_2338_, v_logExceptions_2339_, v___y_2340_, v___y_2341_);
lean_dec_ref(v___y_2340_);
return v_res_2342_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5));
v___x_2363_ = l_Lean_mkCIdent(v___x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig(lean_object* v_x_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1));
lean_inc(v_x_2364_);
v___x_2368_ = l_Lean_Syntax_isOfKind(v_x_2364_, v___x_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; 
lean_dec(v_x_2364_);
v___x_2369_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2366_);
return v___x_2369_;
}
else
{
lean_object* v___f_2370_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v_entries_x3f_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___x_2404_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v_vis_x3f_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v_doc_x3f_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___f_2370_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3));
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2447_ = l_Lean_Syntax_getArg(v_x_2364_, v___x_2404_);
v___x_2448_ = l_Lean_Syntax_isNone(v___x_2447_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2449_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2447_);
v___x_2450_ = l_Lean_Syntax_matchesNull(v___x_2447_, v___x_2449_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; 
lean_dec(v___x_2447_);
lean_dec(v_x_2364_);
v___x_2451_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2366_);
return v___x_2451_;
}
else
{
lean_object* v_doc_x3f_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v_doc_x3f_2452_ = l_Lean_Syntax_getArg(v___x_2447_, v___x_2404_);
lean_dec(v___x_2447_);
v___x_2453_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_2452_);
v___x_2454_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2452_, v___x_2453_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; 
lean_dec(v_doc_x3f_2452_);
lean_dec(v_x_2364_);
v___x_2455_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2366_);
return v___x_2455_;
}
else
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2456_, 0, v_doc_x3f_2452_);
v_doc_x3f_2436_ = v___x_2456_;
v___y_2437_ = v_a_2365_;
v___y_2438_ = v_a_2366_;
goto v___jp_2435_;
}
}
}
else
{
lean_object* v___x_2457_; 
lean_dec(v___x_2447_);
v___x_2457_ = lean_box(0);
v_doc_x3f_2436_ = v___x_2457_;
v___y_2437_ = v_a_2365_;
v___y_2438_ = v_a_2366_;
goto v___jp_2435_;
}
v___jp_2371_:
{
lean_object* v___f_2381_; lean_object* v_binders_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___f_2381_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2));
v_binders_2382_ = l_Lean_Syntax_getArgs(v___y_2372_);
lean_dec(v___y_2372_);
v___x_2383_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6, &l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6);
v___x_2384_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8);
v___x_2385_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_2383_, v___f_2370_, v___x_2384_, v___f_2381_, v___y_2375_, v___y_2377_, v___y_2373_, v___y_2374_, v___y_2376_, v_binders_2382_, v_entries_x3f_2378_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_a_2387_ = lean_ctor_get(v___x_2385_, 1);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2385_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2386_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
v_a_2395_ = lean_ctor_get(v___x_2385_, 0);
v_a_2396_ = lean_ctor_get(v___x_2385_, 1);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2385_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_inc(v_a_2395_);
lean_dec(v___x_2385_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2395_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
v___jp_2405_:
{
lean_object* v___x_2411_; lean_object* v_elabName_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2411_ = lean_unsigned_to_nat(3u);
v_elabName_2412_ = l_Lean_Syntax_getArg(v_x_2364_, v___x_2411_);
v___x_2413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_elabName_2412_);
v___x_2414_ = l_Lean_Syntax_isOfKind(v_elabName_2412_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; 
lean_dec(v_elabName_2412_);
lean_dec(v_vis_x3f_2408_);
lean_dec(v___y_2407_);
lean_dec(v_x_2364_);
v___x_2415_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2410_);
return v___x_2415_;
}
else
{
lean_object* v___x_2416_; lean_object* v_type_2417_; uint8_t v___x_2418_; 
v___x_2416_ = lean_unsigned_to_nat(4u);
v_type_2417_ = l_Lean_Syntax_getArg(v_x_2364_, v___x_2416_);
lean_inc(v_type_2417_);
v___x_2418_ = l_Lean_Syntax_isOfKind(v_type_2417_, v___x_2413_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; 
lean_dec(v_type_2417_);
lean_dec(v_elabName_2412_);
lean_dec(v_vis_x3f_2408_);
lean_dec(v___y_2407_);
lean_dec(v_x_2364_);
v___x_2419_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2410_);
return v___x_2419_;
}
else
{
lean_object* v___x_2420_; lean_object* v_tk_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2420_ = lean_unsigned_to_nat(2u);
v_tk_2421_ = l_Lean_Syntax_getArg(v_x_2364_, v___x_2420_);
v___x_2422_ = lean_unsigned_to_nat(5u);
v___x_2423_ = l_Lean_Syntax_getArg(v_x_2364_, v___x_2422_);
v___x_2424_ = lean_unsigned_to_nat(6u);
v___x_2425_ = l_Lean_Syntax_getArg(v_x_2364_, v___x_2424_);
lean_dec(v_x_2364_);
v___x_2426_ = l_Lean_Syntax_isNone(v___x_2425_);
if (v___x_2426_ == 0)
{
uint8_t v___x_2427_; 
lean_inc(v___x_2425_);
v___x_2427_ = l_Lean_Syntax_matchesNull(v___x_2425_, v___y_2406_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; 
lean_dec(v___x_2425_);
lean_dec(v___x_2423_);
lean_dec(v_tk_2421_);
lean_dec(v_type_2417_);
lean_dec(v_elabName_2412_);
lean_dec(v_vis_x3f_2408_);
lean_dec(v___y_2407_);
v___x_2428_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2410_);
return v___x_2428_;
}
else
{
lean_object* v_entries_x3f_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; 
v_entries_x3f_2429_ = l_Lean_Syntax_getArg(v___x_2425_, v___x_2404_);
lean_dec(v___x_2425_);
v___x_2430_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_2429_);
v___x_2431_ = l_Lean_Syntax_isOfKind(v_entries_x3f_2429_, v___x_2430_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; 
lean_dec(v_entries_x3f_2429_);
lean_dec(v___x_2423_);
lean_dec(v_tk_2421_);
lean_dec(v_type_2417_);
lean_dec(v_elabName_2412_);
lean_dec(v_vis_x3f_2408_);
lean_dec(v___y_2407_);
v___x_2432_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2410_);
return v___x_2432_;
}
else
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2433_, 0, v_entries_x3f_2429_);
v___y_2372_ = v___x_2423_;
v___y_2373_ = v_tk_2421_;
v___y_2374_ = v_elabName_2412_;
v___y_2375_ = v___y_2407_;
v___y_2376_ = v_type_2417_;
v___y_2377_ = v_vis_x3f_2408_;
v_entries_x3f_2378_ = v___x_2433_;
v___y_2379_ = v___y_2409_;
v___y_2380_ = v___y_2410_;
goto v___jp_2371_;
}
}
}
else
{
lean_object* v___x_2434_; 
lean_dec(v___x_2425_);
v___x_2434_ = lean_box(0);
v___y_2372_ = v___x_2423_;
v___y_2373_ = v_tk_2421_;
v___y_2374_ = v_elabName_2412_;
v___y_2375_ = v___y_2407_;
v___y_2376_ = v_type_2417_;
v___y_2377_ = v_vis_x3f_2408_;
v_entries_x3f_2378_ = v___x_2434_;
v___y_2379_ = v___y_2409_;
v___y_2380_ = v___y_2410_;
goto v___jp_2371_;
}
}
}
}
v___jp_2435_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2439_ = lean_unsigned_to_nat(1u);
v___x_2440_ = l_Lean_Syntax_getArg(v_x_2364_, v___x_2439_);
v___x_2441_ = l_Lean_Syntax_isNone(v___x_2440_);
if (v___x_2441_ == 0)
{
uint8_t v___x_2442_; 
lean_inc(v___x_2440_);
v___x_2442_ = l_Lean_Syntax_matchesNull(v___x_2440_, v___x_2439_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; 
lean_dec(v___x_2440_);
lean_dec(v_doc_x3f_2436_);
lean_dec(v_x_2364_);
v___x_2443_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2438_);
return v___x_2443_;
}
else
{
lean_object* v_vis_x3f_2444_; lean_object* v___x_2445_; 
v_vis_x3f_2444_ = l_Lean_Syntax_getArg(v___x_2440_, v___x_2404_);
lean_dec(v___x_2440_);
v___x_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2445_, 0, v_vis_x3f_2444_);
v___y_2406_ = v___x_2439_;
v___y_2407_ = v_doc_x3f_2436_;
v_vis_x3f_2408_ = v___x_2445_;
v___y_2409_ = v___y_2437_;
v___y_2410_ = v___y_2438_;
goto v___jp_2405_;
}
}
else
{
lean_object* v___x_2446_; 
lean_dec(v___x_2440_);
v___x_2446_ = lean_box(0);
v___y_2406_ = v___x_2439_;
v___y_2407_ = v_doc_x3f_2436_;
v_vis_x3f_2408_ = v___x_2446_;
v___y_2409_ = v___y_2437_;
v___y_2410_ = v___y_2438_;
goto v___jp_2405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___boxed(lean_object* v_x_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig(v_x_2458_, v_a_2459_, v_a_2460_);
lean_dec_ref(v_a_2459_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1(){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2469_ = l_Lean_Elab_macroAttribute;
v___x_2470_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1));
v___x_2471_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1));
v___x_2472_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___boxed), 3, 0);
v___x_2473_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2469_, v___x_2470_, v___x_2471_, v___x_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___boxed(lean_object* v_a_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1();
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig(lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_2481_ = lean_unsigned_to_nat(2u);
v___x_2482_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_2480_, v___x_2481_, v_a_2476_, v_a_2477_, v_a_2478_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___boxed(lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig(v_a_2483_, v_a_2484_, v_a_2485_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
return v_res_2487_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___boxed), 4, 0);
v___x_2489_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_2489_, 0, v___x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1(){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1));
v___x_2492_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0);
v___x_2493_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_2491_, v___x_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___boxed(lean_object* v_a_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1();
return v_res_2495_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__0));
v___x_2498_ = l_String_toRawSubstring_x27(v___x_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1(lean_object* v___x_2500_, lean_object* v___x_2501_, lean_object* v___x_2502_, lean_object* v___x_2503_, lean_object* v___x_2504_, lean_object* v_eval_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_quotContext_2508_; lean_object* v_currMacroScope_2509_; lean_object* v_ref_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v_quotContext_2508_ = lean_ctor_get(v___y_2506_, 1);
v_currMacroScope_2509_ = lean_ctor_get(v___y_2506_, 2);
v_ref_2510_ = lean_ctor_get(v___y_2506_, 5);
v___x_2511_ = 0;
v___x_2512_ = l_Lean_SourceInfo_fromRef(v_ref_2510_, v___x_2511_);
v___x_2513_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82));
lean_inc_ref(v___x_2500_);
v___x_2514_ = l_Lean_Name_mkStr4(v___x_2500_, v___x_2501_, v___x_2502_, v___x_2513_);
v___x_2515_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1, &l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1_once, _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1);
v___x_2516_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__2));
lean_inc_ref(v___x_2503_);
v___x_2517_ = l_Lean_Name_mkStr2(v___x_2503_, v___x_2516_);
lean_inc(v_currMacroScope_2509_);
lean_inc(v_quotContext_2508_);
v___x_2518_ = l_Lean_addMacroScope(v_quotContext_2508_, v___x_2517_, v_currMacroScope_2509_);
v___x_2519_ = l_Lean_Name_mkStr4(v___x_2500_, v___x_2504_, v___x_2503_, v___x_2516_);
v___x_2520_ = lean_box(0);
lean_inc(v___x_2519_);
v___x_2521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2519_);
v___x_2523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
lean_ctor_set(v___x_2523_, 1, v___x_2520_);
v___x_2524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2521_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
lean_inc_n(v___x_2512_, 2);
v___x_2525_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2512_);
lean_ctor_set(v___x_2525_, 1, v___x_2515_);
lean_ctor_set(v___x_2525_, 2, v___x_2518_);
lean_ctor_set(v___x_2525_, 3, v___x_2524_);
v___x_2526_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5));
v___x_2527_ = l_Lean_Syntax_node1(v___x_2512_, v___x_2526_, v_eval_2505_);
v___x_2528_ = l_Lean_Syntax_node2(v___x_2512_, v___x_2514_, v___x_2525_, v___x_2527_);
v___x_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v___y_2507_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___boxed(lean_object* v___x_2530_, lean_object* v___x_2531_, lean_object* v___x_2532_, lean_object* v___x_2533_, lean_object* v___x_2534_, lean_object* v_eval_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1(v___x_2530_, v___x_2531_, v___x_2532_, v___x_2533_, v___x_2534_, v_eval_2535_, v___y_2536_, v___y_2537_);
lean_dec_ref(v___y_2536_);
return v_res_2538_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4));
v___x_2558_ = l_Lean_mkCIdent(v___x_2557_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig(lean_object* v_x_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v___x_2562_; uint8_t v___x_2563_; 
v___x_2562_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1));
lean_inc(v_x_2559_);
v___x_2563_ = l_Lean_Syntax_isOfKind(v_x_2559_, v___x_2562_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; 
lean_dec(v_x_2559_);
v___x_2564_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2561_);
return v___x_2564_;
}
else
{
lean_object* v___f_2565_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v_entries_x3f_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___x_2599_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v_vis_x3f_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v_doc_x3f_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___f_2565_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2));
v___x_2599_ = lean_unsigned_to_nat(0u);
v___x_2642_ = l_Lean_Syntax_getArg(v_x_2559_, v___x_2599_);
v___x_2643_ = l_Lean_Syntax_isNone(v___x_2642_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2644_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2642_);
v___x_2645_ = l_Lean_Syntax_matchesNull(v___x_2642_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; 
lean_dec(v___x_2642_);
lean_dec(v_x_2559_);
v___x_2646_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2561_);
return v___x_2646_;
}
else
{
lean_object* v_doc_x3f_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v_doc_x3f_2647_ = l_Lean_Syntax_getArg(v___x_2642_, v___x_2599_);
lean_dec(v___x_2642_);
v___x_2648_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_2647_);
v___x_2649_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2647_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; 
lean_dec(v_doc_x3f_2647_);
lean_dec(v_x_2559_);
v___x_2650_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2561_);
return v___x_2650_;
}
else
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2651_, 0, v_doc_x3f_2647_);
v_doc_x3f_2631_ = v___x_2651_;
v___y_2632_ = v_a_2560_;
v___y_2633_ = v_a_2561_;
goto v___jp_2630_;
}
}
}
else
{
lean_object* v___x_2652_; 
lean_dec(v___x_2642_);
v___x_2652_ = lean_box(0);
v_doc_x3f_2631_ = v___x_2652_;
v___y_2632_ = v_a_2560_;
v___y_2633_ = v_a_2561_;
goto v___jp_2630_;
}
v___jp_2566_:
{
lean_object* v_binders_2576_; lean_object* v___f_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_binders_2576_ = l_Lean_Syntax_getArgs(v___y_2569_);
lean_dec(v___y_2569_);
v___f_2577_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2));
v___x_2578_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5, &l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5_once, _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5);
v___x_2579_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8);
v___x_2580_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_2578_, v___f_2577_, v___x_2579_, v___f_2565_, v___y_2570_, v___y_2568_, v___y_2571_, v___y_2567_, v___y_2572_, v_binders_2576_, v_entries_x3f_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_a_2582_ = lean_ctor_get(v___x_2580_, 1);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2580_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2581_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
v_a_2590_ = lean_ctor_get(v___x_2580_, 0);
v_a_2591_ = lean_ctor_get(v___x_2580_, 1);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2580_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_inc(v_a_2590_);
lean_dec(v___x_2580_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2590_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
v___jp_2600_:
{
lean_object* v___x_2606_; lean_object* v_elabName_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2606_ = lean_unsigned_to_nat(3u);
v_elabName_2607_ = l_Lean_Syntax_getArg(v_x_2559_, v___x_2606_);
v___x_2608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_elabName_2607_);
v___x_2609_ = l_Lean_Syntax_isOfKind(v_elabName_2607_, v___x_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; 
lean_dec(v_elabName_2607_);
lean_dec(v_vis_x3f_2603_);
lean_dec(v___y_2602_);
lean_dec(v_x_2559_);
v___x_2610_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2605_);
return v___x_2610_;
}
else
{
lean_object* v___x_2611_; lean_object* v_type_2612_; uint8_t v___x_2613_; 
v___x_2611_ = lean_unsigned_to_nat(4u);
v_type_2612_ = l_Lean_Syntax_getArg(v_x_2559_, v___x_2611_);
lean_inc(v_type_2612_);
v___x_2613_ = l_Lean_Syntax_isOfKind(v_type_2612_, v___x_2608_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; 
lean_dec(v_type_2612_);
lean_dec(v_elabName_2607_);
lean_dec(v_vis_x3f_2603_);
lean_dec(v___y_2602_);
lean_dec(v_x_2559_);
v___x_2614_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2605_);
return v___x_2614_;
}
else
{
lean_object* v___x_2615_; lean_object* v_tk_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2615_ = lean_unsigned_to_nat(2u);
v_tk_2616_ = l_Lean_Syntax_getArg(v_x_2559_, v___x_2615_);
v___x_2617_ = lean_unsigned_to_nat(5u);
v___x_2618_ = l_Lean_Syntax_getArg(v_x_2559_, v___x_2617_);
v___x_2619_ = lean_unsigned_to_nat(6u);
v___x_2620_ = l_Lean_Syntax_getArg(v_x_2559_, v___x_2619_);
lean_dec(v_x_2559_);
v___x_2621_ = l_Lean_Syntax_isNone(v___x_2620_);
if (v___x_2621_ == 0)
{
uint8_t v___x_2622_; 
lean_inc(v___x_2620_);
v___x_2622_ = l_Lean_Syntax_matchesNull(v___x_2620_, v___y_2601_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; 
lean_dec(v___x_2620_);
lean_dec(v___x_2618_);
lean_dec(v_tk_2616_);
lean_dec(v_type_2612_);
lean_dec(v_elabName_2607_);
lean_dec(v_vis_x3f_2603_);
lean_dec(v___y_2602_);
v___x_2623_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2605_);
return v___x_2623_;
}
else
{
lean_object* v_entries_x3f_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v_entries_x3f_2624_ = l_Lean_Syntax_getArg(v___x_2620_, v___x_2599_);
lean_dec(v___x_2620_);
v___x_2625_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_2624_);
v___x_2626_ = l_Lean_Syntax_isOfKind(v_entries_x3f_2624_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; 
lean_dec(v_entries_x3f_2624_);
lean_dec(v___x_2618_);
lean_dec(v_tk_2616_);
lean_dec(v_type_2612_);
lean_dec(v_elabName_2607_);
lean_dec(v_vis_x3f_2603_);
lean_dec(v___y_2602_);
v___x_2627_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2605_);
return v___x_2627_;
}
else
{
lean_object* v___x_2628_; 
v___x_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_entries_x3f_2624_);
v___y_2567_ = v_elabName_2607_;
v___y_2568_ = v_vis_x3f_2603_;
v___y_2569_ = v___x_2618_;
v___y_2570_ = v___y_2602_;
v___y_2571_ = v_tk_2616_;
v___y_2572_ = v_type_2612_;
v_entries_x3f_2573_ = v___x_2628_;
v___y_2574_ = v___y_2604_;
v___y_2575_ = v___y_2605_;
goto v___jp_2566_;
}
}
}
else
{
lean_object* v___x_2629_; 
lean_dec(v___x_2620_);
v___x_2629_ = lean_box(0);
v___y_2567_ = v_elabName_2607_;
v___y_2568_ = v_vis_x3f_2603_;
v___y_2569_ = v___x_2618_;
v___y_2570_ = v___y_2602_;
v___y_2571_ = v_tk_2616_;
v___y_2572_ = v_type_2612_;
v_entries_x3f_2573_ = v___x_2629_;
v___y_2574_ = v___y_2604_;
v___y_2575_ = v___y_2605_;
goto v___jp_2566_;
}
}
}
}
v___jp_2630_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2634_ = lean_unsigned_to_nat(1u);
v___x_2635_ = l_Lean_Syntax_getArg(v_x_2559_, v___x_2634_);
v___x_2636_ = l_Lean_Syntax_isNone(v___x_2635_);
if (v___x_2636_ == 0)
{
uint8_t v___x_2637_; 
lean_inc(v___x_2635_);
v___x_2637_ = l_Lean_Syntax_matchesNull(v___x_2635_, v___x_2634_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; 
lean_dec(v___x_2635_);
lean_dec(v_doc_x3f_2631_);
lean_dec(v_x_2559_);
v___x_2638_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2633_);
return v___x_2638_;
}
else
{
lean_object* v_vis_x3f_2639_; lean_object* v___x_2640_; 
v_vis_x3f_2639_ = l_Lean_Syntax_getArg(v___x_2635_, v___x_2599_);
lean_dec(v___x_2635_);
v___x_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2640_, 0, v_vis_x3f_2639_);
v___y_2601_ = v___x_2634_;
v___y_2602_ = v_doc_x3f_2631_;
v_vis_x3f_2603_ = v___x_2640_;
v___y_2604_ = v___y_2632_;
v___y_2605_ = v___y_2633_;
goto v___jp_2600_;
}
}
else
{
lean_object* v___x_2641_; 
lean_dec(v___x_2635_);
v___x_2641_ = lean_box(0);
v___y_2601_ = v___x_2634_;
v___y_2602_ = v_doc_x3f_2631_;
v_vis_x3f_2603_ = v___x_2641_;
v___y_2604_ = v___y_2632_;
v___y_2605_ = v___y_2633_;
goto v___jp_2600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___boxed(lean_object* v_x_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig(v_x_2653_, v_a_2654_, v_a_2655_);
lean_dec_ref(v_a_2654_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1(){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2664_ = l_Lean_Elab_macroAttribute;
v___x_2665_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1));
v___x_2666_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1));
v___x_2667_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___boxed), 3, 0);
v___x_2668_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2664_, v___x_2665_, v___x_2666_, v___x_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___boxed(lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1();
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab(lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2675_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_2676_ = lean_unsigned_to_nat(2u);
v___x_2677_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_2675_, v___x_2676_, v_a_2671_, v_a_2672_, v_a_2673_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___boxed(lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab(v_a_2678_, v_a_2679_, v_a_2680_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
return v_res_2682_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___boxed), 4, 0);
v___x_2684_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_2684_, 0, v___x_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1(){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1));
v___x_2687_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0);
v___x_2688_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_2686_, v___x_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___boxed(lean_object* v_a_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1();
return v_res_2690_;
}
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Commands(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_MissingDocs(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ConfigEval_Builtins(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_ConfigEval_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_MissingDocs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ConfigEval_Builtins(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_ConfigEval_Commands(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(uint8_t builtin);
lean_object* initialize_Lean_Linter_MissingDocs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ConfigEval_Builtins(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ConfigEval_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_MissingDocs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_Builtins(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ConfigEval_Builtins(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ConfigEval_Builtins(builtin);
}
#ifdef __cplusplus
}
#endif
