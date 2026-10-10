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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_14_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0(lean_box(0), v___y_11_, v___y_12_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___boxed(lean_object* v_00_u03b1_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0(v_00_u03b1_16_, v___y_17_, v___y_18_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_20_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___redArg(lean_object* v_a_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
return v___x_29_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_21_ = stack[0].m_obj;
lean_object* v___y_22_ = stack[1].m_obj;
lean_object* v___y_23_ = stack[2].m_obj;
lean_object* v___y_24_ = stack[3].m_obj;
lean_object* v___y_25_ = stack[4].m_obj;
lean_object* v___y_26_ = stack[5].m_obj;
lean_object* v___y_27_ = stack[6].m_obj;
lean_object* v_res_30_;
v_res_30_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___redArg(v_a_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___redArg___boxed(lean_object* v_a_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___redArg(v_a_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
return v_res_39_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1(lean_object* v_00_u03b1_40_, lean_object* v_a_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
return v___x_49_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_41_ = stack[1].m_obj;
lean_object* v___y_42_ = stack[2].m_obj;
lean_object* v___y_43_ = stack[3].m_obj;
lean_object* v___y_44_ = stack[4].m_obj;
lean_object* v___y_45_ = stack[5].m_obj;
lean_object* v___y_46_ = stack[6].m_obj;
lean_object* v___y_47_ = stack[7].m_obj;
lean_object* v_res_50_;
v_res_50_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1(lean_box(0), v_a_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
stack->m_obj
 = v_res_50_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed(lean_object* v_00_u03b1_51_, lean_object* v_a_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1(v_00_u03b1_51_, v_a_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_60_;
}
}
lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance(lean_object* v_x_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_vis_x3f_83_; lean_object* v___y_84_; lean_object* v___y_85_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8));
lean_inc(v_x_78_);
v___x_110_ = l_Lean_Syntax_isOfKind(v_x_78_, v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
lean_dec(v_x_78_);
v___x_111_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_111_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = l_Lean_Syntax_getArg(v_x_78_, v___x_112_);
v___x_114_ = l_Lean_Syntax_isNone(v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_113_);
v___x_116_ = l_Lean_Syntax_matchesNull(v___x_113_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
lean_dec(v___x_113_);
lean_dec(v_x_78_);
v___x_117_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_117_;
}
else
{
lean_object* v_vis_x3f_118_; lean_object* v___x_119_; 
v_vis_x3f_118_ = l_Lean_Syntax_getArg(v___x_113_, v___x_112_);
lean_dec(v___x_113_);
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v_vis_x3f_118_);
v_vis_x3f_83_ = v___x_119_;
v___y_84_ = v_a_79_;
v___y_85_ = v_a_80_;
goto v___jp_82_;
}
}
else
{
lean_object* v___x_120_; 
lean_dec(v___x_113_);
v___x_120_ = lean_box(0);
v_vis_x3f_83_ = v___x_120_;
v___y_84_ = v_a_79_;
v___y_85_ = v_a_80_;
goto v___jp_82_;
}
}
v___jp_82_:
{
lean_object* v___x_86_; lean_object* v_kind_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_86_ = lean_unsigned_to_nat(1u);
v_kind_87_ = l_Lean_Syntax_getArg(v_x_78_, v___x_86_);
v___x_88_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
lean_inc(v_kind_87_);
v___x_89_ = l_Lean_Syntax_isOfKind(v_kind_87_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_dec(v_kind_87_);
lean_dec(v_vis_x3f_83_);
lean_dec(v_x_78_);
v___x_90_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v_tk_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_91_ = lean_unsigned_to_nat(2u);
v_tk_92_ = l_Lean_Syntax_getArg(v_x_78_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(3u);
v___x_94_ = l_Lean_Syntax_getArg(v_x_78_, v___x_93_);
lean_dec(v_x_78_);
v___x_95_ = lean_box(0);
lean_inc(v___x_94_);
v___x_96_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_96_, 0, v___x_94_);
lean_closure_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed), 9, 2);
lean_closure_set(v___x_97_, 0, lean_box(0));
lean_closure_set(v___x_97_, 1, v___x_96_);
v___x_98_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_97_, v___y_84_, v___y_85_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_100_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_99_);
lean_dec_ref_known(v___x_98_, 1);
v___x_100_ = l_Lean_Elab_ConfigEval_ensureEvalTerm(v_vis_x3f_83_, v_kind_87_, v_tk_92_, v___x_94_, v_a_99_, v___y_84_, v___y_85_);
return v___x_100_;
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
lean_dec(v___x_94_);
lean_dec(v_tk_92_);
lean_dec(v_kind_87_);
lean_dec(v_vis_x3f_83_);
v_a_101_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_98_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_98_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_78_ = stack[0].m_obj;
lean_object* v_a_79_ = stack[1].m_obj;
lean_object* v_a_80_ = stack[2].m_obj;
lean_object* v_res_121_;
v_res_121_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance(v_x_78_, v_a_79_, v_a_80_);
stack->m_obj
 = v_res_121_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___boxed(lean_object* v_x_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance(v_x_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
return v_res_126_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1(){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_134_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_135_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8));
v___x_136_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___closed__1));
v___x_137_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___boxed), 4, 0);
v___x_138_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_134_, v___x_135_, v___x_136_, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_139_;
v_res_139_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1();
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1___boxed(lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance__1();
return v_res_141_;
}
}
lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance(lean_object* v_x_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_vis_x3f_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1));
lean_inc(v_x_148_);
v___x_180_ = l_Lean_Syntax_isOfKind(v_x_148_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
lean_dec(v_x_148_);
v___x_181_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_181_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = l_Lean_Syntax_getArg(v_x_148_, v___x_182_);
v___x_184_ = l_Lean_Syntax_isNone(v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_183_);
v___x_186_ = l_Lean_Syntax_matchesNull(v___x_183_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_dec(v___x_183_);
lean_dec(v_x_148_);
v___x_187_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_187_;
}
else
{
lean_object* v_vis_x3f_188_; lean_object* v___x_189_; 
v_vis_x3f_188_ = l_Lean_Syntax_getArg(v___x_183_, v___x_182_);
lean_dec(v___x_183_);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v_vis_x3f_188_);
v_vis_x3f_153_ = v___x_189_;
v___y_154_ = v_a_149_;
v___y_155_ = v_a_150_;
goto v___jp_152_;
}
}
else
{
lean_object* v___x_190_; 
lean_dec(v___x_183_);
v___x_190_ = lean_box(0);
v_vis_x3f_153_ = v___x_190_;
v___y_154_ = v_a_149_;
v___y_155_ = v_a_150_;
goto v___jp_152_;
}
}
v___jp_152_:
{
lean_object* v___x_156_; lean_object* v_kind_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_156_ = lean_unsigned_to_nat(1u);
v_kind_157_ = l_Lean_Syntax_getArg(v_x_148_, v___x_156_);
v___x_158_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
lean_inc(v_kind_157_);
v___x_159_ = l_Lean_Syntax_isOfKind(v_kind_157_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
lean_dec(v_kind_157_);
lean_dec(v_vis_x3f_153_);
lean_dec(v_x_148_);
v___x_160_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_160_;
}
else
{
lean_object* v___x_161_; lean_object* v_tk_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_161_ = lean_unsigned_to_nat(2u);
v_tk_162_ = l_Lean_Syntax_getArg(v_x_148_, v___x_161_);
v___x_163_ = lean_unsigned_to_nat(3u);
v___x_164_ = l_Lean_Syntax_getArg(v_x_148_, v___x_163_);
lean_dec(v_x_148_);
v___x_165_ = lean_box(0);
lean_inc(v___x_164_);
v___x_166_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_166_, 0, v___x_164_);
lean_closure_set(v___x_166_, 1, v___x_165_);
v___x_167_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed), 9, 2);
lean_closure_set(v___x_167_, 0, lean_box(0));
lean_closure_set(v___x_167_, 1, v___x_166_);
v___x_168_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_167_, v___y_154_, v___y_155_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v___x_170_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
lean_dec_ref_known(v___x_168_, 1);
v___x_170_ = l_Lean_Elab_ConfigEval_ensureEvalExpr(v_vis_x3f_153_, v_kind_157_, v_tk_162_, v___x_164_, v_a_169_, v___y_154_, v___y_155_);
return v___x_170_;
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec(v___x_164_);
lean_dec(v_tk_162_);
lean_dec(v_kind_157_);
lean_dec(v_vis_x3f_153_);
v_a_171_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_168_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_168_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_148_ = stack[0].m_obj;
lean_object* v_a_149_ = stack[1].m_obj;
lean_object* v_a_150_ = stack[2].m_obj;
lean_object* v_res_191_;
v_res_191_ = l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance(v_x_148_, v_a_149_, v_a_150_);
stack->m_obj
 = v_res_191_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___boxed(lean_object* v_x_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance(v_x_192_, v_a_193_, v_a_194_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
return v_res_196_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1(){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_204_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_205_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1));
v___x_206_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___closed__1));
v___x_207_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___boxed), 4, 0);
v___x_208_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_204_, v___x_205_, v___x_206_, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_209_;
v_res_209_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1();
stack->m_obj
 = v_res_209_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1___boxed(lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___regBuiltin_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance__1();
return v_res_211_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Array_mkArray0___redArg();
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance(lean_object* v_x_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___x_229_; uint8_t v___x_230_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v_vis_x3f_254_; lean_object* v___y_255_; lean_object* v___y_256_; 
v___x_229_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1));
lean_inc(v_x_226_);
v___x_230_ = l_Lean_Syntax_isOfKind(v_x_226_, v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_275_; 
lean_dec(v_x_226_);
v___x_275_ = l_Lean_Macro_throwUnsupported___redArg(v_a_228_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = l_Lean_Syntax_getArg(v_x_226_, v___x_276_);
v___x_278_ = l_Lean_Syntax_isNone(v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_277_);
v___x_280_ = l_Lean_Syntax_matchesNull(v___x_277_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; 
lean_dec(v___x_277_);
lean_dec(v_x_226_);
v___x_281_ = l_Lean_Macro_throwUnsupported___redArg(v_a_228_);
return v___x_281_;
}
else
{
lean_object* v_vis_x3f_282_; lean_object* v___x_283_; 
v_vis_x3f_282_ = l_Lean_Syntax_getArg(v___x_277_, v___x_276_);
lean_dec(v___x_277_);
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v_vis_x3f_282_);
v_vis_x3f_254_ = v___x_283_;
v___y_255_ = v_a_227_;
v___y_256_ = v_a_228_;
goto v___jp_253_;
}
}
else
{
lean_object* v___x_284_; 
lean_dec(v___x_277_);
v___x_284_ = lean_box(0);
v_vis_x3f_254_ = v___x_284_;
v___y_255_ = v_a_227_;
v___y_256_ = v_a_228_;
goto v___jp_253_;
}
}
v___jp_231_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
lean_inc_ref(v___y_239_);
v___x_241_ = l_Array_append___redArg(v___y_239_, v___y_240_);
lean_dec_ref(v___y_240_);
lean_inc_n(v___y_237_, 2);
lean_inc_n(v___y_238_, 3);
v___x_242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_242_, 0, v___y_238_);
lean_ctor_set(v___x_242_, 1, v___y_237_);
lean_ctor_set(v___x_242_, 2, v___x_241_);
v___x_243_ = l_Lean_SourceInfo_fromRef(v___y_233_, v___x_230_);
lean_dec(v___y_233_);
v___x_244_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__2));
lean_inc(v___x_243_);
v___x_245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
lean_inc(v___y_236_);
lean_inc(v___y_234_);
lean_inc_ref(v___x_242_);
lean_inc(v___y_235_);
v___x_246_ = l_Lean_Syntax_node4(v___y_238_, v___y_235_, v___x_242_, v___y_234_, v___x_245_, v___y_236_);
v___x_247_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1));
v___x_248_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__3));
v___x_249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_243_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = l_Lean_Syntax_node4(v___y_238_, v___x_247_, v___x_242_, v___y_234_, v___x_249_, v___y_236_);
v___x_251_ = l_Lean_Syntax_node2(v___y_238_, v___y_237_, v___x_246_, v___x_250_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___y_232_);
return v___x_252_;
}
v___jp_253_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = l_Lean_Syntax_getArg(v_x_226_, v___x_257_);
v___x_259_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
lean_inc(v___x_258_);
v___x_260_ = l_Lean_Syntax_isOfKind(v___x_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
lean_dec(v___x_258_);
lean_dec(v_vis_x3f_254_);
lean_dec(v_x_226_);
v___x_261_ = l_Lean_Macro_throwUnsupported___redArg(v___y_256_);
return v___x_261_;
}
else
{
lean_object* v_ref_262_; lean_object* v___x_263_; lean_object* v_tk_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_ref_262_ = lean_ctor_get(v___y_255_, 5);
v___x_263_ = lean_unsigned_to_nat(2u);
v_tk_264_ = l_Lean_Syntax_getArg(v_x_226_, v___x_263_);
v___x_265_ = lean_unsigned_to_nat(3u);
v___x_266_ = l_Lean_Syntax_getArg(v_x_226_, v___x_265_);
lean_dec(v_x_226_);
v___x_267_ = 0;
v___x_268_ = l_Lean_SourceInfo_fromRef(v_ref_262_, v___x_267_);
v___x_269_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5));
v___x_270_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__8));
v___x_271_ = lean_obj_once(&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6, &l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6_once, _init_l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6);
if (lean_obj_tag(v_vis_x3f_254_) == 1)
{
lean_object* v_val_272_; lean_object* v___x_273_; 
v_val_272_ = lean_ctor_get(v_vis_x3f_254_, 0);
lean_inc(v_val_272_);
lean_dec_ref_known(v_vis_x3f_254_, 1);
v___x_273_ = l_Array_mkArray1___redArg(v_val_272_);
v___y_232_ = v___y_256_;
v___y_233_ = v_tk_264_;
v___y_234_ = v___x_258_;
v___y_235_ = v___x_270_;
v___y_236_ = v___x_266_;
v___y_237_ = v___x_269_;
v___y_238_ = v___x_268_;
v___y_239_ = v___x_271_;
v___y_240_ = v___x_273_;
goto v___jp_231_;
}
else
{
lean_object* v___x_274_; 
lean_dec(v_vis_x3f_254_);
v___x_274_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___y_232_ = v___y_256_;
v___y_233_ = v_tk_264_;
v___y_234_ = v___x_258_;
v___y_235_ = v___x_270_;
v___y_236_ = v___x_266_;
v___y_237_ = v___x_269_;
v___y_238_ = v___x_268_;
v___y_239_ = v___x_271_;
v___y_240_ = v___x_274_;
goto v___jp_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___boxed(lean_object* v_x_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance(v_x_285_, v_a_286_, v_a_287_);
lean_dec_ref(v_a_286_);
return v_res_288_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1(){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_296_ = l_Lean_Elab_macroAttribute;
v___x_297_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__1));
v___x_298_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___closed__1));
v___x_299_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___boxed), 3, 0);
v___x_300_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_296_, v___x_297_, v___x_298_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_301_;
v_res_301_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1();
stack->m_obj
 = v_res_301_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1___boxed(lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___regBuiltin_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance__1();
return v_res_303_;
}
}
lean_object* l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta(lean_object* v_x_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_vis_x3f_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1));
lean_inc(v_x_310_);
v___x_342_ = l_Lean_Syntax_isOfKind(v_x_310_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec(v_x_310_);
v___x_343_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = l_Lean_Syntax_getArg(v_x_310_, v___x_344_);
v___x_346_ = l_Lean_Syntax_isNone(v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_345_);
v___x_348_ = l_Lean_Syntax_matchesNull(v___x_345_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_dec(v___x_345_);
lean_dec(v_x_310_);
v___x_349_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_349_;
}
else
{
lean_object* v_vis_x3f_350_; lean_object* v___x_351_; 
v_vis_x3f_350_ = l_Lean_Syntax_getArg(v___x_345_, v___x_344_);
lean_dec(v___x_345_);
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v_vis_x3f_350_);
v_vis_x3f_315_ = v___x_351_;
v___y_316_ = v_a_311_;
v___y_317_ = v_a_312_;
goto v___jp_314_;
}
}
else
{
lean_object* v___x_352_; 
lean_dec(v___x_345_);
v___x_352_ = lean_box(0);
v_vis_x3f_315_ = v___x_352_;
v___y_316_ = v_a_311_;
v___y_317_ = v_a_312_;
goto v___jp_314_;
}
}
v___jp_314_:
{
lean_object* v___x_318_; lean_object* v_kind_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v_kind_319_ = l_Lean_Syntax_getArg(v_x_310_, v___x_318_);
v___x_320_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
lean_inc(v_kind_319_);
v___x_321_ = l_Lean_Syntax_isOfKind(v_kind_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
lean_dec(v_kind_319_);
lean_dec(v_vis_x3f_315_);
lean_dec(v_x_310_);
v___x_322_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_322_;
}
else
{
lean_object* v___x_323_; lean_object* v_tk_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_323_ = lean_unsigned_to_nat(2u);
v_tk_324_ = l_Lean_Syntax_getArg(v_x_310_, v___x_323_);
v___x_325_ = lean_unsigned_to_nat(3u);
v___x_326_ = l_Lean_Syntax_getArg(v_x_310_, v___x_325_);
lean_dec(v_x_310_);
v___x_327_ = lean_box(0);
lean_inc(v___x_326_);
v___x_328_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_328_, 0, v___x_326_);
lean_closure_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed), 9, 2);
lean_closure_set(v___x_329_, 0, lean_box(0));
lean_closure_set(v___x_329_, 1, v___x_328_);
v___x_330_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_329_, v___y_316_, v___y_317_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_332_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval(v_vis_x3f_315_, v_kind_319_, v_tk_324_, v___x_326_, v_a_331_, v___y_316_, v___y_317_);
return v___x_332_;
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec(v___x_326_);
lean_dec(v_tk_324_);
lean_dec(v_kind_319_);
lean_dec(v_vis_x3f_315_);
v_a_333_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_330_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_330_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_310_ = stack[0].m_obj;
lean_object* v_a_311_ = stack[1].m_obj;
lean_object* v_a_312_ = stack[2].m_obj;
lean_object* v_res_353_;
v_res_353_ = l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta(v_x_310_, v_a_311_, v_a_312_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___boxed(lean_object* v_x_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta(v_x_354_, v_a_355_, v_a_356_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
return v_res_358_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1(){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_366_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_367_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___closed__1));
v___x_368_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___closed__1));
v___x_369_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___boxed), 4, 0);
v___x_370_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_366_, v___x_367_, v___x_368_, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_371_;
v_res_371_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1();
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1___boxed(lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta___regBuiltin_Lean_Elab_ConfigEval_elabDeriveEvalExprUsingMeta__1();
return v_res_373_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(size_t v_sz_374_, size_t v_i_375_, lean_object* v_bs_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = lean_usize_dec_lt(v_i_375_, v_sz_374_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v_bs_376_);
return v___x_378_;
}
else
{
lean_object* v_v_379_; lean_object* v___x_380_; lean_object* v_bs_x27_381_; size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; 
v_v_379_ = lean_array_uget(v_bs_376_, v_i_375_);
v___x_380_ = lean_unsigned_to_nat(0u);
v_bs_x27_381_ = lean_array_uset(v_bs_376_, v_i_375_, v___x_380_);
v___x_382_ = ((size_t)1ULL);
v___x_383_ = lean_usize_add(v_i_375_, v___x_382_);
v___x_384_ = lean_array_uset(v_bs_x27_381_, v_i_375_, v_v_379_);
v_i_375_ = v___x_383_;
v_bs_376_ = v___x_384_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_374_ = stack[0].m_num;
size_t v_i_375_ = stack[1].m_num;
lean_object* v_bs_376_ = stack[2].m_obj;
lean_object* v_res_386_;
v_res_386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(v_sz_374_, v_i_375_, v_bs_376_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0___boxed(lean_object* v_sz_387_, lean_object* v_i_388_, lean_object* v_bs_389_){
_start:
{
size_t v_sz_boxed_390_; size_t v_i_boxed_391_; lean_object* v_res_392_; 
v_sz_boxed_390_ = lean_unbox_usize(v_sz_387_);
lean_dec(v_sz_387_);
v_i_boxed_391_ = lean_unbox_usize(v_i_388_);
lean_dec(v_i_388_);
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(v_sz_boxed_390_, v_i_boxed_391_, v_bs_389_);
return v_res_392_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(size_t v_sz_393_, size_t v_i_394_, lean_object* v_bs_395_){
_start:
{
uint8_t v___x_396_; 
v___x_396_ = lean_usize_dec_lt(v_i_394_, v_sz_393_);
if (v___x_396_ == 0)
{
return v_bs_395_;
}
else
{
lean_object* v_v_397_; lean_object* v___x_398_; lean_object* v_bs_x27_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; 
v_v_397_ = lean_array_uget(v_bs_395_, v_i_394_);
v___x_398_ = lean_unsigned_to_nat(0u);
v_bs_x27_399_ = lean_array_uset(v_bs_395_, v_i_394_, v___x_398_);
v___x_400_ = l_Lean_TSyntax_getId(v_v_397_);
v___x_401_ = l_Lean_Name_eraseMacroScopes(v___x_400_);
lean_dec(v___x_400_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_v_397_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_add(v_i_394_, v___x_403_);
v___x_405_ = lean_array_uset(v_bs_x27_399_, v_i_394_, v___x_402_);
v_i_394_ = v___x_404_;
v_bs_395_ = v___x_405_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_393_ = stack[0].m_num;
size_t v_i_394_ = stack[1].m_num;
lean_object* v_bs_395_ = stack[2].m_obj;
lean_object* v_res_407_;
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(v_sz_393_, v_i_394_, v_bs_395_);
stack->m_obj
 = v_res_407_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1___boxed(lean_object* v_sz_408_, lean_object* v_i_409_, lean_object* v_bs_410_){
_start:
{
size_t v_sz_boxed_411_; size_t v_i_boxed_412_; lean_object* v_res_413_; 
v_sz_boxed_411_ = lean_unbox_usize(v_sz_408_);
lean_dec(v_sz_408_);
v_i_boxed_412_ = lean_unbox_usize(v_i_409_);
lean_dec(v_i_409_);
v_res_413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(v_sz_boxed_411_, v_i_boxed_412_, v_bs_410_);
return v_res_413_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(uint8_t v___x_414_, lean_object* v_as_415_, size_t v_i_416_, size_t v_stop_417_, lean_object* v_b_418_){
_start:
{
lean_object* v___y_420_; uint8_t v___x_424_; 
v___x_424_ = lean_usize_dec_eq(v_i_416_, v_stop_417_);
if (v___x_424_ == 0)
{
lean_object* v_fst_425_; uint8_t v___x_426_; 
v_fst_425_ = lean_ctor_get(v_b_418_, 0);
v___x_426_ = lean_unbox(v_fst_425_);
if (v___x_426_ == 0)
{
lean_object* v_snd_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_435_; 
v_snd_427_ = lean_ctor_get(v_b_418_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v_b_418_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; 
v_unused_436_ = lean_ctor_get(v_b_418_, 0);
lean_dec(v_unused_436_);
v___x_429_ = v_b_418_;
v_isShared_430_ = v_isSharedCheck_435_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snd_427_);
lean_dec(v_b_418_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_435_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = lean_box(v___x_414_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_snd_427_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
v___y_420_ = v___x_433_;
goto v___jp_419_;
}
}
}
else
{
lean_object* v_snd_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_447_; 
v_snd_437_ = lean_ctor_get(v_b_418_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_b_418_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v_b_418_, 0);
lean_dec(v_unused_448_);
v___x_439_ = v_b_418_;
v_isShared_440_ = v_isSharedCheck_447_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snd_437_);
lean_dec(v_b_418_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_447_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_441_ = lean_array_uget_borrowed(v_as_415_, v_i_416_);
lean_inc(v___x_441_);
v___x_442_ = lean_array_push(v_snd_437_, v___x_441_);
v___x_443_ = lean_box(v___x_424_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_442_);
lean_ctor_set(v___x_439_, 0, v___x_443_);
v___x_445_ = v___x_439_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_442_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
v___y_420_ = v___x_445_;
goto v___jp_419_;
}
}
}
}
else
{
return v_b_418_;
}
v___jp_419_:
{
size_t v___x_421_; size_t v___x_422_; 
v___x_421_ = ((size_t)1ULL);
v___x_422_ = lean_usize_add(v_i_416_, v___x_421_);
v_i_416_ = v___x_422_;
v_b_418_ = v___y_420_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_414_ = stack[0].m_num;
lean_object* v_as_415_ = stack[1].m_obj;
size_t v_i_416_ = stack[2].m_num;
size_t v_stop_417_ = stack[3].m_num;
lean_object* v_b_418_ = stack[4].m_obj;
lean_object* v_res_449_;
v_res_449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_414_, v_as_415_, v_i_416_, v_stop_417_, v_b_418_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2___boxed(lean_object* v___x_450_, lean_object* v_as_451_, lean_object* v_i_452_, lean_object* v_stop_453_, lean_object* v_b_454_){
_start:
{
uint8_t v___x_4705__boxed_455_; size_t v_i_boxed_456_; size_t v_stop_boxed_457_; lean_object* v_res_458_; 
v___x_4705__boxed_455_ = lean_unbox(v___x_450_);
v_i_boxed_456_ = lean_unbox_usize(v_i_452_);
lean_dec(v_i_452_);
v_stop_boxed_457_ = lean_unbox_usize(v_stop_453_);
lean_dec(v_stop_453_);
v_res_458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_4705__boxed_455_, v_as_451_, v_i_boxed_456_, v_stop_boxed_457_, v_b_454_);
lean_dec_ref(v_as_451_);
return v_res_458_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(lean_object* v_as_498_, size_t v_sz_499_, size_t v_i_500_, lean_object* v_b_501_){
_start:
{
lean_object* v_a_504_; uint8_t v___x_508_; 
v___x_508_ = lean_usize_dec_lt(v_i_500_, v_sz_499_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v_b_501_);
return v___x_509_;
}
else
{
lean_object* v_fst_510_; lean_object* v_snd_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_677_; 
v_fst_510_ = lean_ctor_get(v_b_501_, 0);
v_snd_511_ = lean_ctor_get(v_b_501_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v_b_501_);
if (v_isSharedCheck_677_ == 0)
{
v___x_513_ = v_b_501_;
v_isShared_514_ = v_isSharedCheck_677_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_snd_511_);
lean_inc(v_fst_510_);
lean_dec(v_b_501_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_677_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___y_516_; lean_object* v_a_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_a_539_ = lean_array_uget_borrowed(v_as_498_, v_i_500_);
v___x_540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1));
lean_inc(v_a_539_);
v___x_541_ = l_Lean_Syntax_isOfKind(v_a_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
lean_del_object(v___x_513_);
v___x_542_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v___x_543_; 
lean_dec_ref_known(v___x_542_, 1);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v_fst_510_);
lean_ctor_set(v___x_543_, 1, v_snd_511_);
v_a_504_ = v___x_543_;
goto v___jp_503_;
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec(v_snd_511_);
lean_dec(v_fst_510_);
v_a_544_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_542_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_542_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = l_Lean_Syntax_getArg(v_a_539_, v___x_552_);
v___x_555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__3));
lean_inc(v___x_554_);
v___x_556_ = l_Lean_Syntax_isOfKind(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; uint8_t v___x_558_; 
lean_del_object(v___x_513_);
v___x_557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__5));
lean_inc(v___x_554_);
v___x_558_ = l_Lean_Syntax_isOfKind(v___x_554_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
lean_dec(v___x_554_);
v___x_559_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v___x_560_; 
lean_dec_ref_known(v___x_559_, 1);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v_fst_510_);
lean_ctor_set(v___x_560_, 1, v_snd_511_);
v_a_504_ = v___x_560_;
goto v___jp_503_;
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v_snd_511_);
lean_dec(v_fst_510_);
v_a_561_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_559_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_559_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_object* v___x_569_; lean_object* v___y_571_; lean_object* v_fst_572_; uint8_t v_snd_573_; lean_object* v___y_579_; lean_object* v_____x_580_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; 
v___x_569_ = l_Lean_Syntax_getArg(v___x_554_, v___x_553_);
if (v___x_556_ == 0)
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7));
lean_inc(v___x_569_);
v___x_655_ = l_Lean_Syntax_isOfKind(v___x_569_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec(v___x_569_);
lean_dec(v___x_554_);
v___x_656_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v___x_657_; 
lean_dec_ref_known(v___x_656_, 1);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v_fst_510_);
lean_ctor_set(v___x_657_, 1, v_snd_511_);
v_a_504_ = v___x_657_;
goto v___jp_503_;
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec(v_snd_511_);
lean_dec(v_fst_510_);
v_a_658_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_656_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
goto v___jp_608_;
}
}
else
{
goto v___jp_608_;
}
v___jp_570_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_574_ = lean_box(0);
v___x_575_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_575_, 0, v___x_569_);
lean_ctor_set(v___x_575_, 1, v_fst_572_);
lean_ctor_set(v___x_575_, 2, v___y_571_);
lean_ctor_set(v___x_575_, 3, v___x_574_);
lean_ctor_set(v___x_575_, 4, v___x_574_);
lean_ctor_set_uint8(v___x_575_, sizeof(void*)*5, v_snd_573_);
v___x_576_ = lean_array_push(v_snd_511_, v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v_fst_510_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v_a_504_ = v___x_577_;
goto v___jp_503_;
}
v___jp_578_:
{
lean_object* v_fst_581_; lean_object* v_snd_582_; uint8_t v___x_583_; 
v_fst_581_ = lean_ctor_get(v_____x_580_, 0);
lean_inc(v_fst_581_);
v_snd_582_ = lean_ctor_get(v_____x_580_, 1);
lean_inc(v_snd_582_);
lean_dec_ref(v_____x_580_);
v___x_583_ = lean_unbox(v_snd_582_);
lean_dec(v_snd_582_);
v___y_571_ = v___y_579_;
v_fst_572_ = v_fst_581_;
v_snd_573_ = v___x_583_;
goto v___jp_570_;
}
v___jp_584_:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = l_Lean_Syntax_getArg(v___y_587_, v___x_553_);
lean_dec(v___y_587_);
lean_inc(v___x_589_);
v___x_590_ = l_Lean_Syntax_matchesNull(v___x_589_, v___x_552_);
if (v___x_590_ == 0)
{
uint8_t v___x_591_; 
v___x_591_ = l_Lean_Syntax_matchesNull(v___x_589_, v___y_585_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
lean_dec(v___y_588_);
v___x_592_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
v___y_579_ = v___y_586_;
v_____x_580_ = v_a_593_;
goto v___jp_578_;
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v___y_586_);
lean_dec(v___x_569_);
lean_dec(v_snd_511_);
lean_dec(v_fst_510_);
v_a_594_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_592_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_592_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_602_ = l_Lean_TSyntax_getId(v___y_588_);
lean_dec(v___y_588_);
v___x_603_ = l_Lean_Name_eraseMacroScopes(v___x_602_);
lean_dec(v___x_602_);
v___x_604_ = 1;
v___y_571_ = v___y_586_;
v_fst_572_ = v___x_603_;
v_snd_573_ = v___x_604_;
goto v___jp_570_;
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
lean_dec(v___x_589_);
v___x_605_ = l_Lean_TSyntax_getId(v___y_588_);
lean_dec(v___y_588_);
v___x_606_ = l_Lean_Name_eraseMacroScopes(v___x_605_);
lean_dec(v___x_605_);
v___x_607_ = 0;
v___y_571_ = v___y_586_;
v_fst_572_ = v___x_606_;
v_snd_573_ = v___x_607_;
goto v___jp_570_;
}
}
v___jp_608_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_609_ = lean_unsigned_to_nat(3u);
v___x_610_ = l_Lean_Syntax_getArg(v___x_554_, v___x_609_);
lean_dec(v___x_554_);
v___x_611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7));
lean_inc(v___x_569_);
v___x_612_ = l_Lean_Syntax_isOfKind(v___x_569_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_613_, 1);
v___y_579_ = v___x_610_;
v_____x_580_ = v_a_614_;
goto v___jp_578_;
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec(v___x_610_);
lean_dec(v___x_569_);
lean_dec(v_snd_511_);
lean_dec(v_fst_510_);
v_a_615_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_613_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_613_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_623_ = l_Lean_Syntax_getArg(v___x_569_, v___x_552_);
v___x_624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9));
lean_inc(v___x_623_);
v___x_625_ = l_Lean_Syntax_isOfKind(v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11));
v___x_627_ = l_Lean_Syntax_isOfKind(v___x_623_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
v___y_579_ = v___x_610_;
v_____x_580_ = v_a_629_;
goto v___jp_578_;
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v___x_610_);
lean_dec(v___x_569_);
lean_dec(v_snd_511_);
lean_dec(v_fst_510_);
v_a_630_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_628_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_628_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_box(0);
v___x_639_ = 1;
v___y_571_ = v___x_610_;
v_fst_572_ = v___x_638_;
v_snd_573_ = v___x_639_;
goto v___jp_570_;
}
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_unsigned_to_nat(2u);
v___x_641_ = l_Lean_Syntax_getArg(v___x_623_, v___x_552_);
if (v___x_556_ == 0)
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v___x_641_);
v___x_643_ = l_Lean_Syntax_isOfKind(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
lean_dec(v___x_641_);
lean_dec(v___x_623_);
v___x_644_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v___y_579_ = v___x_610_;
v_____x_580_ = v_a_645_;
goto v___jp_578_;
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v___x_610_);
lean_dec(v___x_569_);
lean_dec(v_snd_511_);
lean_dec(v_fst_510_);
v_a_646_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_644_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
v___y_585_ = v___x_640_;
v___y_586_ = v___x_610_;
v___y_587_ = v___x_623_;
v___y_588_ = v___x_641_;
goto v___jp_584_;
}
}
else
{
v___y_585_ = v___x_640_;
v___y_586_ = v___x_610_;
v___y_587_ = v___x_623_;
v___y_588_ = v___x_641_;
goto v___jp_584_;
}
}
}
}
}
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_666_ = l_Lean_Syntax_getArg(v___x_554_, v___x_553_);
lean_dec(v___x_554_);
v___x_667_ = l_Lean_Syntax_getArgs(v___x_666_);
lean_dec(v___x_666_);
v___x_668_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___x_669_ = lean_array_get_size(v___x_667_);
v___x_670_ = lean_nat_dec_lt(v___x_552_, v___x_669_);
if (v___x_670_ == 0)
{
lean_dec_ref(v___x_667_);
v___y_516_ = v___x_668_;
goto v___jp_515_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; lean_object* v_snd_676_; 
v___x_671_ = lean_box(v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_668_);
v___x_673_ = ((size_t)0ULL);
v___x_674_ = lean_usize_of_nat(v___x_669_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_556_, v___x_667_, v___x_673_, v___x_674_, v___x_672_);
lean_dec_ref(v___x_667_);
v_snd_676_ = lean_ctor_get(v___x_675_, 1);
lean_inc(v_snd_676_);
lean_dec_ref(v___x_675_);
v___y_516_ = v_snd_676_;
goto v___jp_515_;
}
}
}
v___jp_515_:
{
size_t v_sz_517_; size_t v___x_518_; lean_object* v___x_519_; 
v_sz_517_ = lean_array_size(v___y_516_);
v___x_518_ = ((size_t)0ULL);
v___x_519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__0(v_sz_517_, v___x_518_, v___y_516_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v___x_522_; 
lean_dec_ref_known(v___x_520_, 1);
if (v_isShared_514_ == 0)
{
v___x_522_ = v___x_513_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_fst_510_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_snd_511_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
v_a_504_ = v___x_522_;
goto v___jp_503_;
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_del_object(v___x_513_);
lean_dec(v_snd_511_);
lean_dec(v_fst_510_);
v_a_524_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_520_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_520_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_val_532_; size_t v_sz_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v_val_532_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_val_532_);
lean_dec_ref_known(v___x_519_, 1);
v_sz_533_ = lean_array_size(v_val_532_);
v___x_534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__1(v_sz_533_, v___x_518_, v_val_532_);
v___x_535_ = l_Array_append___redArg(v_fst_510_, v___x_534_);
lean_dec_ref(v___x_534_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_535_);
v___x_537_ = v___x_513_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_snd_511_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
v_a_504_ = v___x_537_;
goto v___jp_503_;
}
}
}
}
}
v___jp_503_:
{
size_t v___x_505_; size_t v___x_506_; 
v___x_505_ = ((size_t)1ULL);
v___x_506_ = lean_usize_add(v_i_500_, v___x_505_);
v_i_500_ = v___x_506_;
v_b_501_ = v_a_504_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_498_ = stack[0].m_obj;
size_t v_sz_499_ = stack[1].m_num;
size_t v_i_500_ = stack[2].m_num;
lean_object* v_b_501_ = stack[3].m_obj;
lean_object* v_res_678_;
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_as_498_, v_sz_499_, v_i_500_, v_b_501_);
stack->m_obj
 = v_res_678_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___boxed(lean_object* v_as_679_, lean_object* v_sz_680_, lean_object* v_i_681_, lean_object* v_b_682_, lean_object* v___y_683_){
_start:
{
size_t v_sz_boxed_684_; size_t v_i_boxed_685_; lean_object* v_res_686_; 
v_sz_boxed_684_ = lean_unbox_usize(v_sz_680_);
lean_dec(v_sz_680_);
v_i_boxed_685_ = lean_unbox_usize(v_i_681_);
lean_dec(v_i_681_);
v_res_686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_as_679_, v_sz_boxed_684_, v_i_boxed_685_, v_b_682_);
lean_dec_ref(v_as_679_);
return v_res_686_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(size_t v_sz_687_, size_t v_i_688_, lean_object* v_bs_689_){
_start:
{
uint8_t v___x_690_; 
v___x_690_ = lean_usize_dec_lt(v_i_688_, v_sz_687_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v_bs_689_);
return v___x_691_;
}
else
{
lean_object* v_v_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_v_692_ = lean_array_uget(v_bs_689_, v_i_688_);
v___x_693_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1));
lean_inc(v_v_692_);
v___x_694_ = l_Lean_Syntax_isOfKind(v_v_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
lean_dec(v_v_692_);
lean_dec_ref(v_bs_689_);
v___x_695_ = lean_box(0);
return v___x_695_;
}
else
{
lean_object* v___x_696_; lean_object* v_bs_x27_697_; size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; 
v___x_696_ = lean_unsigned_to_nat(0u);
v_bs_x27_697_ = lean_array_uset(v_bs_689_, v_i_688_, v___x_696_);
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_add(v_i_688_, v___x_698_);
v___x_700_ = lean_array_uset(v_bs_x27_697_, v_i_688_, v_v_692_);
v_i_688_ = v___x_699_;
v_bs_689_ = v___x_700_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_687_ = stack[0].m_num;
size_t v_i_688_ = stack[1].m_num;
lean_object* v_bs_689_ = stack[2].m_obj;
lean_object* v_res_702_;
v_res_702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(v_sz_687_, v_i_688_, v_bs_689_);
stack->m_obj
 = v_res_702_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3___boxed(lean_object* v_sz_703_, lean_object* v_i_704_, lean_object* v_bs_705_){
_start:
{
size_t v_sz_boxed_706_; size_t v_i_boxed_707_; lean_object* v_res_708_; 
v_sz_boxed_706_ = lean_unbox_usize(v_sz_703_);
lean_dec(v_sz_703_);
v_i_boxed_707_ = lean_unbox_usize(v_i_704_);
lean_dec(v_i_704_);
v_res_708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(v_sz_boxed_706_, v_i_boxed_707_, v_bs_705_);
return v_res_708_;
}
}
lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView(lean_object* v_entries_x3f_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_omitFields_724_; lean_object* v_handlers_725_; lean_object* v___x_728_; lean_object* v_omitFields_729_; lean_object* v___y_731_; 
v___x_728_ = lean_unsigned_to_nat(0u);
v_omitFields_729_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0));
if (lean_obj_tag(v_entries_x3f_719_) == 1)
{
lean_object* v_val_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v_val_759_ = lean_ctor_get(v_entries_x3f_719_, 0);
lean_inc_n(v_val_759_, 2);
lean_dec_ref_known(v_entries_x3f_719_, 1);
v___x_760_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
v___x_761_ = l_Lean_Syntax_isOfKind(v_val_759_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_val_759_);
v___x_762_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = l_Lean_Syntax_getArg(v_val_759_, v___x_771_);
lean_dec(v_val_759_);
v___x_773_ = l_Lean_Syntax_getArgs(v___x_772_);
lean_dec(v___x_772_);
v___x_774_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___x_775_ = lean_array_get_size(v___x_773_);
v___x_776_ = lean_nat_dec_lt(v___x_728_, v___x_775_);
if (v___x_776_ == 0)
{
lean_dec_ref(v___x_773_);
v___y_731_ = v___x_774_;
goto v___jp_730_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; size_t v___x_779_; size_t v___x_780_; lean_object* v___x_781_; lean_object* v_snd_782_; 
v___x_777_ = lean_box(v___x_776_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_774_);
v___x_779_ = ((size_t)0ULL);
v___x_780_ = lean_usize_of_nat(v___x_775_);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_761_, v___x_773_, v___x_779_, v___x_780_, v___x_778_);
lean_dec_ref(v___x_773_);
v_snd_782_ = lean_ctor_get(v___x_781_, 1);
lean_inc(v_snd_782_);
lean_dec_ref(v___x_781_);
v___y_731_ = v_snd_782_;
goto v___jp_730_;
}
}
}
else
{
lean_dec(v_entries_x3f_719_);
v_omitFields_724_ = v_omitFields_729_;
v_handlers_725_ = v_omitFields_729_;
goto v___jp_723_;
}
v___jp_723_:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_omitFields_724_);
lean_ctor_set(v___x_726_, 1, v_handlers_725_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
v___jp_730_:
{
size_t v_sz_732_; size_t v___x_733_; lean_object* v___x_734_; 
v_sz_732_ = lean_array_size(v___y_731_);
v___x_733_ = ((size_t)0ULL);
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(v_sz_732_, v___x_733_, v___y_731_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v___x_735_; lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v___x_735_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
else
{
lean_object* v_val_744_; lean_object* v___x_745_; size_t v_sz_746_; lean_object* v___x_747_; 
v_val_744_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v___x_734_, 1);
v___x_745_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1));
v_sz_746_ = lean_array_size(v_val_744_);
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_val_744_, v_sz_746_, v___x_733_, v___x_745_);
lean_dec(v_val_744_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v_fst_749_; lean_object* v_snd_750_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v_fst_749_ = lean_ctor_get(v_a_748_, 0);
lean_inc(v_fst_749_);
v_snd_750_ = lean_ctor_get(v_a_748_, 1);
lean_inc(v_snd_750_);
lean_dec(v_a_748_);
v_omitFields_724_ = v_fst_749_;
v_handlers_725_ = v_snd_750_;
goto v___jp_723_;
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
v_a_751_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_747_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_747_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_mkEvalConfigItemView_0interp(lean_interpreter_value* stack)
{
lean_object* v_entries_x3f_719_ = stack[0].m_obj;
lean_object* v_a_720_ = stack[1].m_obj;
lean_object* v_a_721_ = stack[2].m_obj;
lean_object* v_res_783_;
v_res_783_ = l_Lean_Elab_ConfigEval_mkEvalConfigItemView(v_entries_x3f_719_, v_a_720_, v_a_721_);
stack->m_obj
 = v_res_783_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView___boxed(lean_object* v_entries_x3f_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Elab_ConfigEval_mkEvalConfigItemView(v_entries_x3f_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
return v_res_788_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4(lean_object* v_as_789_, size_t v_sz_790_, size_t v_i_791_, lean_object* v_b_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_as_789_, v_sz_790_, v_i_791_, v_b_792_);
return v___x_796_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_789_ = stack[0].m_obj;
size_t v_sz_790_ = stack[1].m_num;
size_t v_i_791_ = stack[2].m_num;
lean_object* v_b_792_ = stack[3].m_obj;
lean_object* v___y_793_ = stack[4].m_obj;
lean_object* v___y_794_ = stack[5].m_obj;
lean_object* v_res_797_;
v_res_797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4(v_as_789_, v_sz_790_, v_i_791_, v_b_792_, v___y_793_, v___y_794_);
stack->m_obj
 = v_res_797_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___boxed(lean_object* v_as_798_, lean_object* v_sz_799_, lean_object* v_i_800_, lean_object* v_b_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
size_t v_sz_boxed_805_; size_t v_i_boxed_806_; lean_object* v_res_807_; 
v_sz_boxed_805_ = lean_unbox_usize(v_sz_799_);
lean_dec(v_sz_799_);
v_i_boxed_806_ = lean_unbox_usize(v_i_800_);
lean_dec(v_i_800_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4(v_as_798_, v_sz_boxed_805_, v_i_boxed_806_, v_b_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec_ref(v_as_798_);
return v_res_807_;
}
}
lean_object* l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd(lean_object* v_x_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v_entries_x3f_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1));
lean_inc(v_x_821_);
v___x_861_ = l_Lean_Syntax_isOfKind(v_x_821_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
lean_dec(v_x_821_);
v___x_862_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_862_;
}
else
{
lean_object* v___x_863_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v_vis_x3f_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v_doc_x3f_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_910_ = l_Lean_Syntax_getArg(v_x_821_, v___x_863_);
v___x_911_ = l_Lean_Syntax_isNone(v___x_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_910_);
v___x_913_ = l_Lean_Syntax_matchesNull(v___x_910_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; 
lean_dec(v___x_910_);
lean_dec(v_x_821_);
v___x_914_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_914_;
}
else
{
lean_object* v_doc_x3f_915_; 
v_doc_x3f_915_ = l_Lean_Syntax_getArg(v___x_910_, v___x_863_);
lean_dec(v___x_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_918_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_915_);
v___x_919_ = l_Lean_Syntax_isOfKind(v_doc_x3f_915_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; 
lean_dec(v_doc_x3f_915_);
lean_dec(v_x_821_);
v___x_920_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_920_;
}
else
{
goto v___jp_916_;
}
}
else
{
goto v___jp_916_;
}
v___jp_916_:
{
lean_object* v___x_917_; 
v___x_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_917_, 0, v_doc_x3f_915_);
v_doc_x3f_899_ = v___x_917_;
v___y_900_ = v_a_822_;
v___y_901_ = v_a_823_;
goto v___jp_898_;
}
}
}
else
{
lean_object* v___x_921_; 
lean_dec(v___x_910_);
v___x_921_ = lean_box(0);
v_doc_x3f_899_ = v___x_921_;
v___y_900_ = v_a_822_;
v___y_901_ = v_a_823_;
goto v___jp_898_;
}
v___jp_864_:
{
lean_object* v___x_870_; lean_object* v_kind_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_870_ = lean_unsigned_to_nat(2u);
v_kind_871_ = l_Lean_Syntax_getArg(v_x_821_, v___x_870_);
v___x_872_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
lean_inc(v_kind_871_);
v___x_873_ = l_Lean_Syntax_isOfKind(v_kind_871_, v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec(v_kind_871_);
lean_dec(v_vis_x3f_867_);
lean_dec(v___y_865_);
lean_dec(v_x_821_);
v___x_874_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_874_;
}
else
{
lean_object* v___x_875_; lean_object* v_fn_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_875_ = lean_unsigned_to_nat(4u);
v_fn_876_ = l_Lean_Syntax_getArg(v_x_821_, v___x_875_);
v___x_877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_fn_876_);
v___x_878_ = l_Lean_Syntax_isOfKind(v_fn_876_, v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; 
lean_dec(v_fn_876_);
lean_dec(v_kind_871_);
lean_dec(v_vis_x3f_867_);
lean_dec(v___y_865_);
lean_dec(v_x_821_);
v___x_879_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_879_;
}
else
{
lean_object* v___x_880_; lean_object* v_struct_881_; uint8_t v___x_882_; 
v___x_880_ = lean_unsigned_to_nat(7u);
v_struct_881_ = l_Lean_Syntax_getArg(v_x_821_, v___x_880_);
lean_inc(v_struct_881_);
v___x_882_ = l_Lean_Syntax_isOfKind(v_struct_881_, v___x_877_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
lean_dec(v_struct_881_);
lean_dec(v_fn_876_);
lean_dec(v_kind_871_);
lean_dec(v_vis_x3f_867_);
lean_dec(v___y_865_);
lean_dec(v_x_821_);
v___x_883_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_883_;
}
else
{
lean_object* v___x_884_; lean_object* v_tk_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_884_ = lean_unsigned_to_nat(3u);
v_tk_885_ = l_Lean_Syntax_getArg(v_x_821_, v___x_884_);
v___x_886_ = lean_unsigned_to_nat(5u);
v___x_887_ = l_Lean_Syntax_getArg(v_x_821_, v___x_886_);
v___x_888_ = lean_unsigned_to_nat(8u);
v___x_889_ = l_Lean_Syntax_getArg(v_x_821_, v___x_888_);
lean_dec(v_x_821_);
v___x_890_ = l_Lean_Syntax_isNone(v___x_889_);
if (v___x_890_ == 0)
{
uint8_t v___x_891_; 
lean_inc(v___x_889_);
v___x_891_ = l_Lean_Syntax_matchesNull(v___x_889_, v___y_866_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_dec(v___x_889_);
lean_dec(v___x_887_);
lean_dec(v_tk_885_);
lean_dec(v_struct_881_);
lean_dec(v_fn_876_);
lean_dec(v_kind_871_);
lean_dec(v_vis_x3f_867_);
lean_dec(v___y_865_);
v___x_892_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_892_;
}
else
{
lean_object* v_entries_x3f_893_; 
v_entries_x3f_893_ = l_Lean_Syntax_getArg(v___x_889_, v___x_863_);
lean_dec(v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_893_);
v___x_895_ = l_Lean_Syntax_isOfKind(v_entries_x3f_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec(v_entries_x3f_893_);
lean_dec(v___x_887_);
lean_dec(v_tk_885_);
lean_dec(v_struct_881_);
lean_dec(v_fn_876_);
lean_dec(v_kind_871_);
lean_dec(v_vis_x3f_867_);
lean_dec(v___y_865_);
v___x_896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_896_;
}
else
{
v___y_849_ = v___y_865_;
v___y_850_ = v___y_868_;
v___y_851_ = v_vis_x3f_867_;
v___y_852_ = v_tk_885_;
v___y_853_ = v___y_869_;
v___y_854_ = v_entries_x3f_893_;
v___y_855_ = v___x_887_;
v___y_856_ = v_fn_876_;
v___y_857_ = v_struct_881_;
v___y_858_ = v_kind_871_;
goto v___jp_848_;
}
}
else
{
v___y_849_ = v___y_865_;
v___y_850_ = v___y_868_;
v___y_851_ = v_vis_x3f_867_;
v___y_852_ = v_tk_885_;
v___y_853_ = v___y_869_;
v___y_854_ = v_entries_x3f_893_;
v___y_855_ = v___x_887_;
v___y_856_ = v_fn_876_;
v___y_857_ = v_struct_881_;
v___y_858_ = v_kind_871_;
goto v___jp_848_;
}
}
}
else
{
lean_object* v___x_897_; 
lean_dec(v___x_889_);
v___x_897_ = lean_box(0);
v___y_826_ = v___y_865_;
v___y_827_ = v_vis_x3f_867_;
v___y_828_ = v_tk_885_;
v___y_829_ = v_fn_876_;
v___y_830_ = v___x_887_;
v___y_831_ = v_struct_881_;
v___y_832_ = v_kind_871_;
v_entries_x3f_833_ = v___x_897_;
v___y_834_ = v___y_868_;
v___y_835_ = v___y_869_;
goto v___jp_825_;
}
}
}
}
}
v___jp_898_:
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = l_Lean_Syntax_getArg(v_x_821_, v___x_902_);
v___x_904_ = l_Lean_Syntax_isNone(v___x_903_);
if (v___x_904_ == 0)
{
uint8_t v___x_905_; 
lean_inc(v___x_903_);
v___x_905_ = l_Lean_Syntax_matchesNull(v___x_903_, v___x_902_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec(v___x_903_);
lean_dec(v_doc_x3f_899_);
lean_dec(v_x_821_);
v___x_906_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_906_;
}
else
{
lean_object* v_vis_x3f_907_; lean_object* v___x_908_; 
v_vis_x3f_907_ = l_Lean_Syntax_getArg(v___x_903_, v___x_863_);
lean_dec(v___x_903_);
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v_vis_x3f_907_);
v___y_865_ = v_doc_x3f_899_;
v___y_866_ = v___x_902_;
v_vis_x3f_867_ = v___x_908_;
v___y_868_ = v___y_900_;
v___y_869_ = v___y_901_;
goto v___jp_864_;
}
}
else
{
lean_object* v___x_909_; 
lean_dec(v___x_903_);
v___x_909_ = lean_box(0);
v___y_865_ = v_doc_x3f_899_;
v___y_866_ = v___x_902_;
v_vis_x3f_867_ = v___x_909_;
v___y_868_ = v___y_900_;
v___y_869_ = v___y_901_;
goto v___jp_864_;
}
}
}
v___jp_825_:
{
lean_object* v_binders_836_; lean_object* v___x_837_; 
v_binders_836_ = l_Lean_Syntax_getArgs(v___y_830_);
lean_dec(v___y_830_);
v___x_837_ = l_Lean_Elab_ConfigEval_mkEvalConfigItemView(v_entries_x3f_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v___x_839_ = l_Lean_Elab_ConfigEval_defEvalConfigItem(v___y_826_, v___y_827_, v___y_832_, v___y_828_, v___y_831_, v___y_829_, v_binders_836_, v_a_838_, v___y_834_, v___y_835_);
return v___x_839_;
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_binders_836_);
lean_dec(v___y_832_);
lean_dec(v___y_831_);
lean_dec(v___y_829_);
lean_dec(v___y_828_);
lean_dec(v___y_827_);
lean_dec(v___y_826_);
v_a_840_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_837_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_837_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
v___jp_848_:
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_859_, 0, v___y_854_);
v___y_826_ = v___y_849_;
v___y_827_ = v___y_851_;
v___y_828_ = v___y_852_;
v___y_829_ = v___y_856_;
v___y_830_ = v___y_855_;
v___y_831_ = v___y_857_;
v___y_832_ = v___y_858_;
v_entries_x3f_833_ = v___x_859_;
v___y_834_ = v___y_850_;
v___y_835_ = v___y_853_;
goto v___jp_825_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_821_ = stack[0].m_obj;
lean_object* v_a_822_ = stack[1].m_obj;
lean_object* v_a_823_ = stack[2].m_obj;
lean_object* v_res_922_;
v_res_922_ = l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd(v_x_821_, v_a_822_, v_a_823_);
stack->m_obj
 = v_res_922_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___boxed(lean_object* v_x_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd(v_x_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
return v_res_927_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1(){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_935_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_936_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1));
v___x_937_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1));
v___x_938_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___boxed), 4, 0);
v___x_939_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_935_, v___x_936_, v___x_937_, v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_940_;
v_res_940_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1();
stack->m_obj
 = v_res_940_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___boxed(lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1();
return v_res_942_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd(lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_949_ = lean_unsigned_to_nat(2u);
v___x_950_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_948_, v___x_949_, v_a_944_, v_a_945_, v_a_946_);
return v___x_950_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_944_ = stack[0].m_obj;
lean_object* v_a_945_ = stack[1].m_obj;
lean_object* v_a_946_ = stack[2].m_obj;
lean_object* v_res_951_;
v_res_951_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd(v_a_944_, v_a_945_, v_a_946_);
stack->m_obj
 = v_res_951_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___boxed(lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd(v_a_952_, v_a_953_, v_a_954_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
return v_res_956_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___boxed), 4, 0);
v___x_958_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1(){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1));
v___x_961_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0);
v___x_962_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_960_, v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_963_;
v_res_963_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1();
stack->m_obj
 = v_res_963_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___boxed(lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1();
return v_res_965_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(size_t v_sz_966_, size_t v_i_967_, lean_object* v_bs_968_){
_start:
{
uint8_t v___x_969_; 
v___x_969_ = lean_usize_dec_lt(v_i_967_, v_sz_966_);
if (v___x_969_ == 0)
{
return v_bs_968_;
}
else
{
lean_object* v_v_970_; lean_object* v___x_971_; lean_object* v_bs_x27_972_; size_t v___x_973_; size_t v___x_974_; lean_object* v___x_975_; 
v_v_970_ = lean_array_uget(v_bs_968_, v_i_967_);
v___x_971_ = lean_unsigned_to_nat(0u);
v_bs_x27_972_ = lean_array_uset(v_bs_968_, v_i_967_, v___x_971_);
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_add(v_i_967_, v___x_973_);
v___x_975_ = lean_array_uset(v_bs_x27_972_, v_i_967_, v_v_970_);
v_i_967_ = v___x_974_;
v_bs_968_ = v___x_975_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_966_ = stack[0].m_num;
size_t v_i_967_ = stack[1].m_num;
lean_object* v_bs_968_ = stack[2].m_obj;
lean_object* v_res_977_;
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_966_, v_i_967_, v_bs_968_);
stack->m_obj
 = v_res_977_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0___boxed(lean_object* v_sz_978_, lean_object* v_i_979_, lean_object* v_bs_980_){
_start:
{
size_t v_sz_boxed_981_; size_t v_i_boxed_982_; lean_object* v_res_983_; 
v_sz_boxed_981_ = lean_unbox_usize(v_sz_978_);
lean_dec(v_sz_978_);
v_i_boxed_982_ = lean_unbox_usize(v_i_979_);
lean_dec(v_i_979_);
v_res_983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_boxed_981_, v_i_boxed_982_, v_bs_980_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(lean_object* v_stx_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1));
lean_inc(v_stx_1009_);
v___x_1013_ = l_Lean_Syntax_isOfKind(v_stx_1009_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3));
lean_inc(v_stx_1009_);
v___x_1015_ = l_Lean_Syntax_isOfKind(v_stx_1009_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5));
lean_inc(v_stx_1009_);
v___x_1017_ = l_Lean_Syntax_isOfKind(v_stx_1009_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7));
lean_inc(v_stx_1009_);
v___x_1019_ = l_Lean_Syntax_isOfKind(v_stx_1009_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_1021_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1009_, v___x_1020_, v_a_1010_, v_a_1011_);
lean_dec(v_stx_1009_);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1022_ = lean_unsigned_to_nat(0u);
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = l_Lean_Syntax_getArg(v_stx_1009_, v___x_1023_);
v___x_1025_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1024_);
v___x_1026_ = l_Lean_Syntax_matchesNull(v___x_1024_, v___x_1025_);
if (v___x_1026_ == 0)
{
uint8_t v___x_1027_; 
v___x_1027_ = l_Lean_Syntax_matchesNull(v___x_1024_, v___x_1022_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_1029_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1009_, v___x_1028_, v_a_1010_, v_a_1011_);
lean_dec(v_stx_1009_);
return v___x_1029_;
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1030_ = l_Lean_mkHole(v_stx_1009_, v___x_1026_);
lean_dec(v_stx_1009_);
v___x_1031_ = lean_mk_empty_array_with_capacity(v___x_1023_);
v___x_1032_ = lean_array_push(v___x_1031_, v___x_1030_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v_a_1011_);
return v___x_1033_;
}
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_Syntax_getArg(v___x_1024_, v___x_1022_);
lean_dec(v___x_1024_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v___x_1034_);
v___x_1040_ = l_Lean_Syntax_isOfKind(v___x_1034_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_dec(v___x_1034_);
v___x_1041_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_1042_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1009_, v___x_1041_, v_a_1010_, v_a_1011_);
lean_dec(v_stx_1009_);
return v___x_1042_;
}
else
{
lean_dec(v_stx_1009_);
goto v___jp_1035_;
}
}
else
{
lean_dec(v_stx_1009_);
goto v___jp_1035_;
}
v___jp_1035_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = lean_mk_empty_array_with_capacity(v___x_1023_);
v___x_1037_ = lean_array_push(v___x_1036_, v___x_1034_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v_a_1011_);
return v___x_1038_;
}
}
}
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1043_ = lean_unsigned_to_nat(2u);
v___x_1044_ = l_Lean_Syntax_getArg(v_stx_1009_, v___x_1043_);
v___x_1045_ = l_Lean_Syntax_matchesNull(v___x_1044_, v___x_1043_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_1047_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1009_, v___x_1046_, v_a_1010_, v_a_1011_);
lean_dec(v_stx_1009_);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_ids_1050_; size_t v_sz_1051_; size_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1048_ = lean_unsigned_to_nat(1u);
v___x_1049_ = l_Lean_Syntax_getArg(v_stx_1009_, v___x_1048_);
lean_dec(v_stx_1009_);
v_ids_1050_ = l_Lean_Syntax_getArgs(v___x_1049_);
lean_dec(v___x_1049_);
v_sz_1051_ = lean_array_size(v_ids_1050_);
v___x_1052_ = ((size_t)0ULL);
v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_1051_, v___x_1052_, v_ids_1050_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v_a_1011_);
return v___x_1054_;
}
}
}
else
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___y_1058_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = l_Lean_Syntax_getArg(v_stx_1009_, v___x_1055_);
v___x_1064_ = lean_unsigned_to_nat(2u);
v___x_1065_ = l_Lean_Syntax_getArg(v_stx_1009_, v___x_1064_);
v___x_1066_ = l_Lean_Syntax_isNone(v___x_1065_);
if (v___x_1066_ == 0)
{
uint8_t v___x_1067_; 
v___x_1067_ = l_Lean_Syntax_matchesNull(v___x_1065_, v___x_1064_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_dec(v___x_1056_);
v___x_1068_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_1069_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1009_, v___x_1068_, v_a_1010_, v_a_1011_);
lean_dec(v_stx_1009_);
return v___x_1069_;
}
else
{
lean_dec(v_stx_1009_);
v___y_1058_ = v_a_1011_;
goto v___jp_1057_;
}
}
else
{
lean_dec(v___x_1065_);
lean_dec(v_stx_1009_);
v___y_1058_ = v_a_1011_;
goto v___jp_1057_;
}
v___jp_1057_:
{
lean_object* v_ids_1059_; size_t v_sz_1060_; size_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_ids_1059_ = l_Lean_Syntax_getArgs(v___x_1056_);
lean_dec(v___x_1056_);
v_sz_1060_ = lean_array_size(v_ids_1059_);
v___x_1061_ = ((size_t)0ULL);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_1060_, v___x_1061_, v_ids_1059_);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___y_1058_);
return v___x_1063_;
}
}
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___y_1073_; lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = l_Lean_Syntax_getArg(v_stx_1009_, v___x_1070_);
v___x_1079_ = lean_unsigned_to_nat(2u);
v___x_1080_ = l_Lean_Syntax_getArg(v_stx_1009_, v___x_1079_);
v___x_1081_ = l_Lean_Syntax_isNone(v___x_1080_);
if (v___x_1081_ == 0)
{
uint8_t v___x_1082_; 
v___x_1082_ = l_Lean_Syntax_matchesNull(v___x_1080_, v___x_1079_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v___x_1071_);
v___x_1083_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_1084_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1009_, v___x_1083_, v_a_1010_, v_a_1011_);
lean_dec(v_stx_1009_);
return v___x_1084_;
}
else
{
lean_dec(v_stx_1009_);
v___y_1073_ = v_a_1011_;
goto v___jp_1072_;
}
}
else
{
lean_dec(v___x_1080_);
lean_dec(v_stx_1009_);
v___y_1073_ = v_a_1011_;
goto v___jp_1072_;
}
v___jp_1072_:
{
lean_object* v_ids_1074_; size_t v_sz_1075_; size_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_ids_1074_ = l_Lean_Syntax_getArgs(v___x_1071_);
lean_dec(v___x_1071_);
v_sz_1075_ = lean_array_size(v_ids_1074_);
v___x_1076_ = ((size_t)0ULL);
v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_1075_, v___x_1076_, v_ids_1074_);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___y_1073_);
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___boxed(lean_object* v_stx_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(v_stx_1085_, v_a_1086_, v_a_1087_);
lean_dec_ref(v_a_1086_);
return v_res_1088_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(lean_object* v_as_1089_, size_t v_i_1090_, size_t v_stop_1091_, lean_object* v_b_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_a_1096_; lean_object* v_a_1097_; uint8_t v___x_1101_; 
v___x_1101_ = lean_usize_dec_eq(v_i_1090_, v_stop_1091_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_array_uget_borrowed(v_as_1089_, v_i_1090_);
lean_inc(v___x_1102_);
v___x_1103_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(v___x_1102_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v_a_1105_; lean_object* v___x_1106_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
v_a_1105_ = lean_ctor_get(v___x_1103_, 1);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1103_, 2);
v___x_1106_ = l_Array_append___redArg(v_b_1092_, v_a_1104_);
lean_dec(v_a_1104_);
v_a_1096_ = v___x_1106_;
v_a_1097_ = v_a_1105_;
goto v___jp_1095_;
}
else
{
lean_dec_ref(v_b_1092_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1107_; lean_object* v_a_1108_; 
v_a_1107_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1107_);
v_a_1108_ = lean_ctor_get(v___x_1103_, 1);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1103_, 2);
v_a_1096_ = v_a_1107_;
v_a_1097_ = v_a_1108_;
goto v___jp_1095_;
}
else
{
return v___x_1103_;
}
}
}
else
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v_b_1092_);
lean_ctor_set(v___x_1109_, 1, v___y_1094_);
return v___x_1109_;
}
v___jp_1095_:
{
size_t v___x_1098_; size_t v___x_1099_; 
v___x_1098_ = ((size_t)1ULL);
v___x_1099_ = lean_usize_add(v_i_1090_, v___x_1098_);
v_i_1090_ = v___x_1099_;
v_b_1092_ = v_a_1096_;
v___y_1094_ = v_a_1097_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1089_ = stack[0].m_obj;
size_t v_i_1090_ = stack[1].m_num;
size_t v_stop_1091_ = stack[2].m_num;
lean_object* v_b_1092_ = stack[3].m_obj;
lean_object* v___y_1093_ = stack[4].m_obj;
lean_object* v___y_1094_ = stack[5].m_obj;
lean_object* v_res_1110_;
v_res_1110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_as_1089_, v_i_1090_, v_stop_1091_, v_b_1092_, v___y_1093_, v___y_1094_);
stack->m_obj
 = v_res_1110_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3___boxed(lean_object* v_as_1111_, lean_object* v_i_1112_, lean_object* v_stop_1113_, lean_object* v_b_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
size_t v_i_boxed_1117_; size_t v_stop_boxed_1118_; lean_object* v_res_1119_; 
v_i_boxed_1117_ = lean_unbox_usize(v_i_1112_);
lean_dec(v_i_1112_);
v_stop_boxed_1118_ = lean_unbox_usize(v_stop_1113_);
lean_dec(v_stop_1113_);
v_res_1119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_as_1111_, v_i_boxed_1117_, v_stop_boxed_1118_, v_b_1114_, v___y_1115_, v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_as_1111_);
return v_res_1119_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(size_t v_sz_1120_, size_t v_i_1121_, lean_object* v_bs_1122_){
_start:
{
uint8_t v___x_1123_; 
v___x_1123_ = lean_usize_dec_lt(v_i_1121_, v_sz_1120_);
if (v___x_1123_ == 0)
{
return v_bs_1122_;
}
else
{
lean_object* v_v_1124_; lean_object* v___x_1125_; lean_object* v_bs_x27_1126_; size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
v_v_1124_ = lean_array_uget(v_bs_1122_, v_i_1121_);
v___x_1125_ = lean_unsigned_to_nat(0u);
v_bs_x27_1126_ = lean_array_uset(v_bs_1122_, v_i_1121_, v___x_1125_);
v___x_1127_ = ((size_t)1ULL);
v___x_1128_ = lean_usize_add(v_i_1121_, v___x_1127_);
v___x_1129_ = lean_array_uset(v_bs_x27_1126_, v_i_1121_, v_v_1124_);
v_i_1121_ = v___x_1128_;
v_bs_1122_ = v___x_1129_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1120_ = stack[0].m_num;
size_t v_i_1121_ = stack[1].m_num;
lean_object* v_bs_1122_ = stack[2].m_obj;
lean_object* v_res_1131_;
v_res_1131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(v_sz_1120_, v_i_1121_, v_bs_1122_);
stack->m_obj
 = v_res_1131_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2___boxed(lean_object* v_sz_1132_, lean_object* v_i_1133_, lean_object* v_bs_1134_){
_start:
{
size_t v_sz_boxed_1135_; size_t v_i_boxed_1136_; lean_object* v_res_1137_; 
v_sz_boxed_1135_ = lean_unbox_usize(v_sz_1132_);
lean_dec(v_sz_1132_);
v_i_boxed_1136_ = lean_unbox_usize(v_i_1133_);
lean_dec(v_i_1133_);
v_res_1137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(v_sz_boxed_1135_, v_i_boxed_1136_, v_bs_1134_);
return v_res_1137_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(size_t v_sz_1138_, size_t v_i_1139_, lean_object* v_bs_1140_){
_start:
{
uint8_t v___x_1141_; 
v___x_1141_ = lean_usize_dec_lt(v_i_1139_, v_sz_1138_);
if (v___x_1141_ == 0)
{
return v_bs_1140_;
}
else
{
lean_object* v_v_1142_; lean_object* v___x_1143_; lean_object* v_bs_x27_1144_; size_t v___x_1145_; size_t v___x_1146_; lean_object* v___x_1147_; 
v_v_1142_ = lean_array_uget(v_bs_1140_, v_i_1139_);
v___x_1143_ = lean_unsigned_to_nat(0u);
v_bs_x27_1144_ = lean_array_uset(v_bs_1140_, v_i_1139_, v___x_1143_);
v___x_1145_ = ((size_t)1ULL);
v___x_1146_ = lean_usize_add(v_i_1139_, v___x_1145_);
v___x_1147_ = lean_array_uset(v_bs_x27_1144_, v_i_1139_, v_v_1142_);
v_i_1139_ = v___x_1146_;
v_bs_1140_ = v___x_1147_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1138_ = stack[0].m_num;
size_t v_i_1139_ = stack[1].m_num;
lean_object* v_bs_1140_ = stack[2].m_obj;
lean_object* v_res_1149_;
v_res_1149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_1138_, v_i_1139_, v_bs_1140_);
stack->m_obj
 = v_res_1149_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0___boxed(lean_object* v_sz_1150_, lean_object* v_i_1151_, lean_object* v_bs_1152_){
_start:
{
size_t v_sz_boxed_1153_; size_t v_i_boxed_1154_; lean_object* v_res_1155_; 
v_sz_boxed_1153_ = lean_unbox_usize(v_sz_1150_);
lean_dec(v_sz_1150_);
v_i_boxed_1154_ = lean_unbox_usize(v_i_1151_);
lean_dec(v_i_1151_);
v_res_1155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_boxed_1153_, v_i_boxed_1154_, v_bs_1152_);
return v_res_1155_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(size_t v_sz_1156_, size_t v_i_1157_, lean_object* v_bs_1158_){
_start:
{
uint8_t v___x_1159_; 
v___x_1159_ = lean_usize_dec_lt(v_i_1157_, v_sz_1156_);
if (v___x_1159_ == 0)
{
return v_bs_1158_;
}
else
{
lean_object* v_v_1160_; lean_object* v___x_1161_; lean_object* v_bs_x27_1162_; size_t v___x_1163_; size_t v___x_1164_; lean_object* v___x_1165_; 
v_v_1160_ = lean_array_uget(v_bs_1158_, v_i_1157_);
v___x_1161_ = lean_unsigned_to_nat(0u);
v_bs_x27_1162_ = lean_array_uset(v_bs_1158_, v_i_1157_, v___x_1161_);
v___x_1163_ = ((size_t)1ULL);
v___x_1164_ = lean_usize_add(v_i_1157_, v___x_1163_);
v___x_1165_ = lean_array_uset(v_bs_x27_1162_, v_i_1157_, v_v_1160_);
v_i_1157_ = v___x_1164_;
v_bs_1158_ = v___x_1165_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1156_ = stack[0].m_num;
size_t v_i_1157_ = stack[1].m_num;
lean_object* v_bs_1158_ = stack[2].m_obj;
lean_object* v_res_1167_;
v_res_1167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(v_sz_1156_, v_i_1157_, v_bs_1158_);
stack->m_obj
 = v_res_1167_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1___boxed(lean_object* v_sz_1168_, lean_object* v_i_1169_, lean_object* v_bs_1170_){
_start:
{
size_t v_sz_boxed_1171_; size_t v_i_boxed_1172_; lean_object* v_res_1173_; 
v_sz_boxed_1171_ = lean_unbox_usize(v_sz_1168_);
lean_dec(v_sz_1168_);
v_i_boxed_1172_ = lean_unbox_usize(v_i_1169_);
lean_dec(v_i_1169_);
v_res_1173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(v_sz_boxed_1171_, v_i_boxed_1172_, v_bs_1170_);
return v_res_1173_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6));
v___x_1183_ = l_String_toRawSubstring_x27(v___x_1182_);
return v___x_1183_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25));
v___x_1224_ = l_String_toRawSubstring_x27(v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53));
v___x_1297_ = l_String_toRawSubstring_x27(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56));
v___x_1301_ = l_String_toRawSubstring_x27(v___x_1300_);
return v___x_1301_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59));
v___x_1306_ = l_String_toRawSubstring_x27(v___x_1305_);
return v___x_1306_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74));
v___x_1338_ = l_Lean_mkIdent(v___x_1337_);
return v___x_1338_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77));
v___x_1343_ = l_Lean_mkIdent(v___x_1342_);
return v___x_1343_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80));
v___x_1348_ = l_Lean_mkIdent(v___x_1347_);
return v___x_1348_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84));
v___x_1357_ = l_String_toRawSubstring_x27(v___x_1356_);
return v___x_1357_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92));
v___x_1377_ = l_String_toRawSubstring_x27(v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98));
v___x_1389_ = l_String_toRawSubstring_x27(v___x_1388_);
return v___x_1389_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73));
v___x_1395_ = l_String_toRawSubstring_x27(v___x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(lean_object* v_monad_1413_, lean_object* v_mkMonadAdapt_1414_, lean_object* v_logExceptionsDefault_1415_, lean_object* v_mkLogExceptionsTerm_1416_, lean_object* v_doc_x3f_1417_, lean_object* v_vis_x3f_1418_, lean_object* v_tk_1419_, lean_object* v_elabName_1420_, lean_object* v_type_1421_, lean_object* v_binders_1422_, lean_object* v_entries_x3f_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; size_t v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; size_t v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; size_t v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; size_t v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; size_t v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; size_t v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v_a_1739_; lean_object* v_a_1740_; lean_object* v___y_1843_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0));
v___x_1428_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0));
v___x_1429_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1));
v___x_1855_ = lean_array_get_size(v_binders_1422_);
v___x_1856_ = lean_nat_dec_lt(v___x_1426_, v___x_1855_);
if (v___x_1856_ == 0)
{
v_a_1739_ = v___x_1427_;
v_a_1740_ = v_a_1425_;
goto v___jp_1738_;
}
else
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_nat_dec_le(v___x_1855_, v___x_1855_);
if (v___x_1857_ == 0)
{
if (v___x_1856_ == 0)
{
v_a_1739_ = v___x_1427_;
v_a_1740_ = v_a_1425_;
goto v___jp_1738_;
}
else
{
size_t v___x_1858_; size_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = ((size_t)0ULL);
v___x_1859_ = lean_usize_of_nat(v___x_1855_);
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_binders_1422_, v___x_1858_, v___x_1859_, v___x_1427_, v_a_1424_, v_a_1425_);
v___y_1843_ = v___x_1860_;
goto v___jp_1842_;
}
}
else
{
size_t v___x_1861_; size_t v___x_1862_; lean_object* v___x_1863_; 
v___x_1861_ = ((size_t)0ULL);
v___x_1862_ = lean_usize_of_nat(v___x_1855_);
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_binders_1422_, v___x_1861_, v___x_1862_, v___x_1427_, v_a_1424_, v_a_1425_);
v___y_1843_ = v___x_1863_;
goto v___jp_1842_;
}
}
v___jp_1430_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; size_t v_sz_1485_; lean_object* v___x_1486_; size_t v_sz_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_inc_ref_n(v___y_1435_, 2);
v___x_1467_ = l_Array_append___redArg(v___y_1435_, v___y_1466_);
lean_dec_ref(v___y_1466_);
lean_inc_n(v___y_1462_, 18);
lean_inc_n(v___y_1431_, 77);
v___x_1468_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1468_, 0, v___y_1431_);
lean_ctor_set(v___x_1468_, 1, v___y_1462_);
lean_ctor_set(v___x_1468_, 2, v___x_1467_);
lean_inc_n(v___y_1434_, 22);
v___x_1469_ = l_Lean_Syntax_node7(v___y_1431_, v___y_1458_, v___y_1457_, v___y_1434_, v___x_1468_, v___y_1434_, v___y_1434_, v___y_1434_, v___y_1434_);
v___x_1470_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1));
lean_inc_ref_n(v___y_1440_, 4);
v___x_1471_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___y_1440_, v___x_1470_);
v___x_1472_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2));
v___x_1473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___y_1431_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3));
v___x_1475_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___y_1440_, v___x_1474_);
lean_inc_n(v___y_1453_, 2);
v___x_1476_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1476_, 0, v___y_1453_);
lean_ctor_set(v___x_1476_, 1, v___y_1462_);
lean_ctor_set(v___x_1476_, 2, v___x_1427_);
v___x_1477_ = lean_unsigned_to_nat(2u);
v___x_1478_ = lean_mk_empty_array_with_capacity(v___x_1477_);
v___x_1479_ = lean_array_push(v___x_1478_, v_elabName_1420_);
v___x_1480_ = lean_array_push(v___x_1479_, v___x_1476_);
v___x_1481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1481_, 0, v___y_1453_);
lean_ctor_set(v___x_1481_, 1, v___x_1475_);
lean_ctor_set(v___x_1481_, 2, v___x_1480_);
v___x_1482_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4));
v___x_1483_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___y_1440_, v___x_1482_);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(v___y_1445_, v___y_1459_, v_binders_1422_);
v_sz_1485_ = lean_array_size(v___x_1484_);
v___x_1486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(v_sz_1485_, v___y_1459_, v___x_1484_);
v_sz_1487_ = lean_array_size(v___x_1486_);
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_1487_, v___y_1459_, v___x_1486_);
v___x_1489_ = l_Array_append___redArg(v___y_1435_, v___x_1488_);
lean_dec_ref(v___x_1488_);
v___x_1490_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1));
lean_inc_ref(v___y_1452_);
v___x_1491_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___y_1431_);
lean_ctor_set(v___x_1491_, 1, v___y_1452_);
v___x_1492_ = l_Lean_Syntax_node1(v___y_1431_, v___y_1462_, v___y_1439_);
v___x_1493_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5));
v___x_1494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___y_1431_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7);
v___x_1496_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9));
lean_inc_n(v___y_1442_, 5);
lean_inc_n(v___y_1461_, 5);
v___x_1497_ = l_Lean_addMacroScope(v___y_1461_, v___x_1496_, v___y_1442_);
lean_inc_n(v___y_1463_, 5);
v___x_1498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1496_);
lean_ctor_set(v___x_1498_, 1, v___y_1463_);
v___x_1499_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10));
lean_inc_n(v___y_1454_, 8);
v___x_1500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
lean_ctor_set(v___x_1500_, 1, v___y_1454_);
v___x_1501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1498_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v___x_1502_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1502_, 0, v___y_1431_);
lean_ctor_set(v___x_1502_, 1, v___x_1495_);
lean_ctor_set(v___x_1502_, 2, v___x_1497_);
lean_ctor_set(v___x_1502_, 3, v___x_1501_);
lean_inc_ref_n(v___x_1494_, 4);
v___x_1503_ = l_Lean_Syntax_node2(v___y_1431_, v___y_1462_, v___x_1494_, v___x_1502_);
lean_inc_ref(v___y_1448_);
v___x_1504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___y_1431_);
lean_ctor_set(v___x_1504_, 1, v___y_1448_);
lean_inc_ref_n(v___x_1504_, 3);
lean_inc_ref_n(v___x_1491_, 3);
v___x_1505_ = l_Lean_Syntax_node5(v___y_1431_, v___x_1490_, v___x_1491_, v___x_1492_, v___x_1503_, v___y_1434_, v___x_1504_);
v___x_1506_ = lean_array_push(v___x_1489_, v___x_1505_);
v___x_1507_ = l_Lean_Syntax_node1(v___y_1431_, v___y_1462_, v___y_1460_);
lean_inc_n(v_type_1421_, 2);
v___x_1508_ = l_Lean_Syntax_node2(v___y_1431_, v___y_1462_, v___x_1494_, v_type_1421_);
v___x_1509_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12));
lean_inc_ref(v___y_1443_);
v___x_1510_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___y_1431_);
lean_ctor_set(v___x_1510_, 1, v___y_1443_);
v___x_1511_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14));
v___x_1512_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16));
v___x_1513_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17));
v___x_1514_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___y_1431_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18));
v___x_1516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___y_1431_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
lean_inc_ref(v___x_1516_);
lean_inc_ref(v___x_1514_);
v___x_1517_ = l_Lean_Syntax_node2(v___y_1431_, v___x_1512_, v___x_1514_, v___x_1516_);
v___x_1518_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20));
v___x_1519_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22));
v___x_1520_ = l_Lean_Syntax_node1(v___y_1431_, v___x_1519_, v___y_1434_);
v___x_1521_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24));
v___x_1522_ = l_Lean_Syntax_node1(v___y_1431_, v___x_1521_, v___y_1434_);
v___x_1523_ = l_Lean_Syntax_node6(v___y_1431_, v___x_1518_, v___x_1514_, v___y_1434_, v___x_1520_, v___x_1522_, v___y_1434_, v___x_1516_);
v___x_1524_ = l_Lean_Syntax_node2(v___y_1431_, v___x_1511_, v___x_1517_, v___x_1523_);
lean_inc_ref_n(v___x_1510_, 5);
v___x_1525_ = l_Lean_Syntax_node2(v___y_1431_, v___x_1509_, v___x_1510_, v___x_1524_);
v___x_1526_ = l_Lean_Syntax_node1(v___y_1431_, v___y_1462_, v___x_1525_);
v___x_1527_ = l_Lean_Syntax_node5(v___y_1431_, v___x_1490_, v___x_1491_, v___x_1507_, v___x_1508_, v___x_1526_, v___x_1504_);
v___x_1528_ = lean_array_push(v___x_1506_, v___x_1527_);
v___x_1529_ = l_Lean_Syntax_node1(v___y_1431_, v___y_1462_, v___y_1464_);
v___x_1530_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26);
v___x_1531_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27));
v___x_1532_ = l_Lean_addMacroScope(v___y_1461_, v___x_1531_, v___y_1442_);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___y_1463_);
v___x_1534_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29));
v___x_1535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v___y_1454_);
v___x_1536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1533_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1537_, 0, v___y_1431_);
lean_ctor_set(v___x_1537_, 1, v___x_1530_);
lean_ctor_set(v___x_1537_, 2, v___x_1532_);
lean_ctor_set(v___x_1537_, 3, v___x_1536_);
v___x_1538_ = l_Lean_Syntax_node2(v___y_1431_, v___y_1462_, v___x_1494_, v___x_1537_);
v___x_1539_ = l_Lean_Syntax_node2(v___y_1431_, v___x_1509_, v___x_1510_, v_logExceptionsDefault_1415_);
v___x_1540_ = l_Lean_Syntax_node1(v___y_1431_, v___y_1462_, v___x_1539_);
v___x_1541_ = l_Lean_Syntax_node5(v___y_1431_, v___x_1490_, v___x_1491_, v___x_1529_, v___x_1538_, v___x_1540_, v___x_1504_);
v___x_1542_ = lean_array_push(v___x_1528_, v___x_1541_);
v___x_1543_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1543_, 0, v___y_1431_);
lean_ctor_set(v___x_1543_, 1, v___y_1462_);
lean_ctor_set(v___x_1543_, 2, v___x_1542_);
v___x_1544_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31));
v___x_1545_ = l_Lean_Syntax_node1(v___y_1431_, v___y_1462_, v_type_1421_);
lean_inc(v___x_1545_);
lean_inc_n(v___y_1436_, 4);
v___x_1546_ = l_Lean_Syntax_node2(v___y_1431_, v___y_1436_, v_monad_1413_, v___x_1545_);
v___x_1547_ = l_Lean_Syntax_node2(v___y_1431_, v___x_1544_, v___x_1494_, v___x_1546_);
v___x_1548_ = l_Lean_Syntax_node1(v___y_1431_, v___y_1462_, v___x_1547_);
v___x_1549_ = l_Lean_Syntax_node2(v___y_1431_, v___x_1483_, v___x_1543_, v___x_1548_);
v___x_1550_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32));
v___x_1551_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___y_1440_, v___x_1550_);
v___x_1552_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33));
v___x_1553_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34));
v___x_1554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___y_1431_);
lean_ctor_set(v___x_1554_, 1, v___x_1552_);
v___x_1555_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36));
v___x_1556_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38));
v___x_1557_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40));
v___x_1558_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41));
v___x_1559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___y_1431_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43));
v___x_1561_ = l_Lean_Syntax_node1(v___y_1431_, v___x_1560_, v___y_1434_);
v___x_1562_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45));
v___x_1563_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47));
v___x_1564_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49));
lean_inc_ref(v___y_1446_);
v___x_1565_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1565_, 0, v___y_1431_);
lean_ctor_set(v___x_1565_, 1, v___y_1446_);
lean_ctor_set(v___x_1565_, 2, v___y_1437_);
lean_ctor_set(v___x_1565_, 3, v___y_1454_);
v___x_1566_ = l_Lean_Syntax_node1(v___y_1431_, v___x_1564_, v___x_1565_);
lean_inc_ref_n(v___y_1447_, 5);
v___x_1567_ = l_String_toRawSubstring_x27(v___y_1447_);
v___x_1568_ = l_Lean_Name_mkStr1(v___y_1447_);
v___x_1569_ = l_Lean_addMacroScope(v___y_1461_, v___x_1568_, v___y_1442_);
lean_inc_ref_n(v___y_1441_, 2);
lean_inc_ref_n(v___y_1465_, 2);
v___x_1570_ = l_Lean_Name_mkStr4(v___x_1428_, v___y_1465_, v___y_1441_, v___y_1447_);
lean_inc(v___x_1570_);
v___x_1571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___y_1463_);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
v___x_1573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v___y_1454_);
v___x_1574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1571_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1575_, 0, v___y_1431_);
lean_ctor_set(v___x_1575_, 1, v___x_1567_);
lean_ctor_set(v___x_1575_, 2, v___x_1569_);
lean_ctor_set(v___x_1575_, 3, v___x_1574_);
v___x_1576_ = l_Lean_Syntax_node2(v___y_1431_, v___y_1436_, v___x_1575_, v___x_1545_);
v___x_1577_ = l_Lean_Syntax_node2(v___y_1431_, v___x_1544_, v___x_1494_, v___x_1576_);
v___x_1578_ = l_Lean_Syntax_node1(v___y_1431_, v___y_1462_, v___x_1577_);
v___x_1579_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51));
v___x_1580_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52));
v___x_1581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___y_1431_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_Syntax_node2(v___y_1431_, v___x_1579_, v___x_1581_, v___y_1451_);
v___x_1583_ = l_Array_append___redArg(v___y_1435_, v___y_1450_);
lean_dec_ref(v___y_1450_);
v___x_1584_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1584_, 0, v___y_1431_);
lean_ctor_set(v___x_1584_, 1, v___y_1462_);
lean_ctor_set(v___x_1584_, 2, v___x_1583_);
v___x_1585_ = l_Lean_Syntax_node2(v___y_1431_, v___y_1436_, v___x_1582_, v___x_1584_);
v___x_1586_ = l_Lean_Syntax_node5(v___y_1431_, v___x_1563_, v___x_1566_, v___y_1434_, v___x_1578_, v___x_1510_, v___x_1585_);
v___x_1587_ = l_Lean_Syntax_node1(v___y_1431_, v___x_1562_, v___x_1586_);
lean_inc(v___x_1561_);
lean_inc_ref(v___x_1559_);
v___x_1588_ = l_Lean_Syntax_node4(v___y_1431_, v___x_1557_, v___x_1559_, v___y_1434_, v___x_1561_, v___x_1587_);
v___x_1589_ = l_Lean_Syntax_node2(v___y_1431_, v___x_1556_, v___x_1588_, v___y_1434_);
lean_inc_ref(v___y_1449_);
v___x_1590_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1590_, 0, v___y_1431_);
lean_ctor_set(v___x_1590_, 1, v___y_1449_);
lean_ctor_set(v___x_1590_, 2, v___y_1433_);
lean_ctor_set(v___x_1590_, 3, v___y_1454_);
v___x_1591_ = l_Lean_Syntax_node1(v___y_1431_, v___x_1564_, v___x_1590_);
v___x_1592_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54);
v___x_1593_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55));
v___x_1594_ = l_Lean_Name_mkStr2(v___y_1447_, v___x_1593_);
v___x_1595_ = l_Lean_addMacroScope(v___y_1461_, v___x_1594_, v___y_1442_);
v___x_1596_ = l_Lean_Name_mkStr5(v___x_1428_, v___y_1465_, v___y_1441_, v___y_1447_, v___x_1593_);
v___x_1597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
lean_ctor_set(v___x_1597_, 1, v___y_1463_);
v___x_1598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v___y_1454_);
v___x_1599_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1599_, 0, v___y_1431_);
lean_ctor_set(v___x_1599_, 1, v___x_1592_);
lean_ctor_set(v___x_1599_, 2, v___x_1595_);
lean_ctor_set(v___x_1599_, 3, v___x_1598_);
v___x_1600_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57);
v___x_1601_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58));
v___x_1602_ = l_Lean_addMacroScope(v___y_1461_, v___x_1601_, v___y_1442_);
v___x_1603_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1603_, 0, v___y_1431_);
lean_ctor_set(v___x_1603_, 1, v___x_1600_);
lean_ctor_set(v___x_1603_, 2, v___x_1602_);
lean_ctor_set(v___x_1603_, 3, v___y_1454_);
v___x_1604_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60);
v___x_1605_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61));
v___x_1606_ = l_Lean_addMacroScope(v___y_1461_, v___x_1605_, v___y_1442_);
v___x_1607_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62));
v___x_1608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v___y_1463_);
v___x_1609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_ctor_set(v___x_1609_, 1, v___y_1454_);
v___x_1610_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1610_, 0, v___y_1431_);
lean_ctor_set(v___x_1610_, 1, v___x_1604_);
lean_ctor_set(v___x_1610_, 2, v___x_1606_);
lean_ctor_set(v___x_1610_, 3, v___x_1609_);
v___x_1611_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64));
v___x_1612_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65));
v___x_1613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___y_1431_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
lean_inc_ref(v___x_1613_);
v___x_1614_ = l_Lean_Syntax_node3(v___y_1431_, v___x_1611_, v___x_1613_, v___x_1613_, v_type_1421_);
v___x_1615_ = l_Lean_Syntax_node1(v___y_1431_, v___y_1462_, v___x_1614_);
v___x_1616_ = l_Lean_Syntax_node2(v___y_1431_, v___y_1436_, v___x_1610_, v___x_1615_);
v___x_1617_ = l_Lean_Syntax_node5(v___y_1431_, v___y_1455_, v___x_1491_, v___x_1603_, v___x_1510_, v___x_1616_, v___x_1504_);
v___x_1618_ = l_Lean_Syntax_node1(v___y_1431_, v___y_1462_, v___x_1617_);
v___x_1619_ = l_Lean_Syntax_node2(v___y_1431_, v___y_1436_, v___x_1599_, v___x_1618_);
v___x_1620_ = l_Lean_Syntax_node5(v___y_1431_, v___x_1563_, v___x_1591_, v___y_1434_, v___y_1434_, v___x_1510_, v___x_1619_);
v___x_1621_ = l_Lean_Syntax_node1(v___y_1431_, v___x_1562_, v___x_1620_);
v___x_1622_ = l_Lean_Syntax_node4(v___y_1431_, v___x_1557_, v___x_1559_, v___y_1434_, v___x_1561_, v___x_1621_);
v___x_1623_ = l_Lean_Syntax_node2(v___y_1431_, v___x_1556_, v___x_1622_, v___y_1434_);
v___x_1624_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67));
v___x_1625_ = l_Lean_Syntax_node1(v___y_1431_, v___x_1624_, v___y_1456_);
v___x_1626_ = l_Lean_Syntax_node2(v___y_1431_, v___x_1556_, v___x_1625_, v___y_1434_);
v___x_1627_ = l_Lean_Syntax_node3(v___y_1431_, v___y_1462_, v___x_1589_, v___x_1623_, v___x_1626_);
v___x_1628_ = l_Lean_Syntax_node1(v___y_1431_, v___x_1555_, v___x_1627_);
v___x_1629_ = l_Lean_Syntax_node2(v___y_1431_, v___x_1553_, v___x_1554_, v___x_1628_);
v___x_1630_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70));
v___x_1631_ = l_Lean_Syntax_node2(v___y_1431_, v___x_1630_, v___y_1434_, v___y_1434_);
v___x_1632_ = l_Lean_Syntax_node4(v___y_1431_, v___x_1551_, v___x_1510_, v___x_1629_, v___x_1631_, v___y_1434_);
v___x_1633_ = l_Lean_Syntax_node5(v___y_1431_, v___x_1471_, v___x_1473_, v___x_1481_, v___x_1549_, v___x_1632_, v___y_1434_);
v___x_1634_ = l_Lean_Syntax_node2(v___y_1431_, v___y_1438_, v___x_1469_, v___x_1633_);
v___x_1635_ = l_Lean_Syntax_node2(v___y_1431_, v___y_1462_, v___y_1444_, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v___y_1432_);
return v___x_1636_;
}
v___jp_1637_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_inc_ref(v___y_1642_);
v___x_1673_ = l_Array_append___redArg(v___y_1642_, v___y_1672_);
lean_dec_ref(v___y_1672_);
lean_inc(v___y_1668_);
lean_inc(v___y_1638_);
v___x_1674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1674_, 0, v___y_1638_);
lean_ctor_set(v___x_1674_, 1, v___y_1668_);
lean_ctor_set(v___x_1674_, 2, v___x_1673_);
if (lean_obj_tag(v_vis_x3f_1418_) == 1)
{
lean_object* v_val_1675_; lean_object* v___x_1676_; 
v_val_1675_ = lean_ctor_get(v_vis_x3f_1418_, 0);
lean_inc(v_val_1675_);
lean_dec_ref_known(v_vis_x3f_1418_, 1);
v___x_1676_ = l_Array_mkArray1___redArg(v_val_1675_);
v___y_1431_ = v___y_1638_;
v___y_1432_ = v___y_1641_;
v___y_1433_ = v___y_1640_;
v___y_1434_ = v___y_1639_;
v___y_1435_ = v___y_1642_;
v___y_1436_ = v___y_1644_;
v___y_1437_ = v___y_1643_;
v___y_1438_ = v___y_1646_;
v___y_1439_ = v___y_1645_;
v___y_1440_ = v___y_1647_;
v___y_1441_ = v___y_1649_;
v___y_1442_ = v___y_1648_;
v___y_1443_ = v___y_1650_;
v___y_1444_ = v___y_1651_;
v___y_1445_ = v___y_1652_;
v___y_1446_ = v___y_1653_;
v___y_1447_ = v___y_1654_;
v___y_1448_ = v___y_1655_;
v___y_1449_ = v___y_1656_;
v___y_1450_ = v___y_1657_;
v___y_1451_ = v___y_1658_;
v___y_1452_ = v___y_1659_;
v___y_1453_ = v___y_1660_;
v___y_1454_ = v___y_1661_;
v___y_1455_ = v___y_1662_;
v___y_1456_ = v___y_1663_;
v___y_1457_ = v___x_1674_;
v___y_1458_ = v___y_1664_;
v___y_1459_ = v___y_1666_;
v___y_1460_ = v___y_1665_;
v___y_1461_ = v___y_1667_;
v___y_1462_ = v___y_1668_;
v___y_1463_ = v___y_1669_;
v___y_1464_ = v___y_1670_;
v___y_1465_ = v___y_1671_;
v___y_1466_ = v___x_1676_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1677_; 
lean_dec(v_vis_x3f_1418_);
v___x_1677_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___y_1431_ = v___y_1638_;
v___y_1432_ = v___y_1641_;
v___y_1433_ = v___y_1640_;
v___y_1434_ = v___y_1639_;
v___y_1435_ = v___y_1642_;
v___y_1436_ = v___y_1644_;
v___y_1437_ = v___y_1643_;
v___y_1438_ = v___y_1646_;
v___y_1439_ = v___y_1645_;
v___y_1440_ = v___y_1647_;
v___y_1441_ = v___y_1649_;
v___y_1442_ = v___y_1648_;
v___y_1443_ = v___y_1650_;
v___y_1444_ = v___y_1651_;
v___y_1445_ = v___y_1652_;
v___y_1446_ = v___y_1653_;
v___y_1447_ = v___y_1654_;
v___y_1448_ = v___y_1655_;
v___y_1449_ = v___y_1656_;
v___y_1450_ = v___y_1657_;
v___y_1451_ = v___y_1658_;
v___y_1452_ = v___y_1659_;
v___y_1453_ = v___y_1660_;
v___y_1454_ = v___y_1661_;
v___y_1455_ = v___y_1662_;
v___y_1456_ = v___y_1663_;
v___y_1457_ = v___x_1674_;
v___y_1458_ = v___y_1664_;
v___y_1459_ = v___y_1666_;
v___y_1460_ = v___y_1665_;
v___y_1461_ = v___y_1667_;
v___y_1462_ = v___y_1668_;
v___y_1463_ = v___y_1669_;
v___y_1464_ = v___y_1670_;
v___y_1465_ = v___y_1671_;
v___y_1466_ = v___x_1677_;
goto v___jp_1430_;
}
}
v___jp_1678_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_inc_ref(v___y_1683_);
v___x_1717_ = l_Array_append___redArg(v___y_1683_, v___y_1716_);
lean_dec_ref(v___y_1716_);
lean_inc(v___y_1711_);
lean_inc_n(v___y_1679_, 2);
v___x_1718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1718_, 0, v___y_1679_);
lean_ctor_set(v___x_1718_, 1, v___y_1711_);
lean_ctor_set(v___x_1718_, 2, v___x_1717_);
v___x_1719_ = lean_unsigned_to_nat(9u);
v___x_1720_ = lean_mk_empty_array_with_capacity(v___x_1719_);
lean_inc(v___y_1681_);
v___x_1721_ = lean_array_push(v___x_1720_, v___y_1681_);
v___x_1722_ = lean_array_push(v___x_1721_, v___y_1715_);
v___x_1723_ = lean_array_push(v___x_1722_, v___y_1693_);
v___x_1724_ = lean_array_push(v___x_1723_, v___y_1685_);
lean_inc(v___y_1701_);
v___x_1725_ = lean_array_push(v___x_1724_, v___y_1701_);
v___x_1726_ = lean_array_push(v___x_1725_, v___y_1709_);
v___x_1727_ = lean_array_push(v___x_1726_, v___y_1697_);
lean_inc(v_type_1421_);
v___x_1728_ = lean_array_push(v___x_1727_, v_type_1421_);
v___x_1729_ = lean_array_push(v___x_1728_, v___x_1718_);
lean_inc(v___y_1684_);
v___x_1730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1730_, 0, v___y_1679_);
lean_ctor_set(v___x_1730_, 1, v___y_1684_);
lean_ctor_set(v___x_1730_, 2, v___x_1729_);
v___x_1731_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71));
lean_inc_ref_n(v___y_1689_, 2);
v___x_1732_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___y_1689_, v___x_1731_);
v___x_1733_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72));
v___x_1734_ = l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___y_1689_, v___x_1733_);
if (lean_obj_tag(v_doc_x3f_1417_) == 1)
{
lean_object* v_val_1735_; lean_object* v___x_1736_; 
v_val_1735_ = lean_ctor_get(v_doc_x3f_1417_, 0);
lean_inc(v_val_1735_);
lean_dec_ref_known(v_doc_x3f_1417_, 1);
v___x_1736_ = l_Array_mkArray1___redArg(v_val_1735_);
v___y_1638_ = v___y_1679_;
v___y_1639_ = v___y_1681_;
v___y_1640_ = v___y_1680_;
v___y_1641_ = v___y_1682_;
v___y_1642_ = v___y_1683_;
v___y_1643_ = v___y_1686_;
v___y_1644_ = v___y_1687_;
v___y_1645_ = v___y_1688_;
v___y_1646_ = v___x_1732_;
v___y_1647_ = v___y_1689_;
v___y_1648_ = v___y_1690_;
v___y_1649_ = v___y_1691_;
v___y_1650_ = v___y_1692_;
v___y_1651_ = v___x_1730_;
v___y_1652_ = v___y_1694_;
v___y_1653_ = v___y_1695_;
v___y_1654_ = v___y_1696_;
v___y_1655_ = v___y_1698_;
v___y_1656_ = v___y_1700_;
v___y_1657_ = v___y_1699_;
v___y_1658_ = v___y_1701_;
v___y_1659_ = v___y_1702_;
v___y_1660_ = v___y_1704_;
v___y_1661_ = v___y_1703_;
v___y_1662_ = v___y_1705_;
v___y_1663_ = v___y_1706_;
v___y_1664_ = v___x_1734_;
v___y_1665_ = v___y_1708_;
v___y_1666_ = v___y_1707_;
v___y_1667_ = v___y_1710_;
v___y_1668_ = v___y_1711_;
v___y_1669_ = v___y_1712_;
v___y_1670_ = v___y_1713_;
v___y_1671_ = v___y_1714_;
v___y_1672_ = v___x_1736_;
goto v___jp_1637_;
}
else
{
lean_object* v___x_1737_; 
lean_dec(v_doc_x3f_1417_);
v___x_1737_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___y_1638_ = v___y_1679_;
v___y_1639_ = v___y_1681_;
v___y_1640_ = v___y_1680_;
v___y_1641_ = v___y_1682_;
v___y_1642_ = v___y_1683_;
v___y_1643_ = v___y_1686_;
v___y_1644_ = v___y_1687_;
v___y_1645_ = v___y_1688_;
v___y_1646_ = v___x_1732_;
v___y_1647_ = v___y_1689_;
v___y_1648_ = v___y_1690_;
v___y_1649_ = v___y_1691_;
v___y_1650_ = v___y_1692_;
v___y_1651_ = v___x_1730_;
v___y_1652_ = v___y_1694_;
v___y_1653_ = v___y_1695_;
v___y_1654_ = v___y_1696_;
v___y_1655_ = v___y_1698_;
v___y_1656_ = v___y_1700_;
v___y_1657_ = v___y_1699_;
v___y_1658_ = v___y_1701_;
v___y_1659_ = v___y_1702_;
v___y_1660_ = v___y_1704_;
v___y_1661_ = v___y_1703_;
v___y_1662_ = v___y_1705_;
v___y_1663_ = v___y_1706_;
v___y_1664_ = v___x_1734_;
v___y_1665_ = v___y_1708_;
v___y_1666_ = v___y_1707_;
v___y_1667_ = v___y_1710_;
v___y_1668_ = v___y_1711_;
v___y_1669_ = v___y_1712_;
v___y_1670_ = v___y_1713_;
v___y_1671_ = v___y_1714_;
v___y_1672_ = v___x_1737_;
goto v___jp_1637_;
}
}
v___jp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74));
v___x_1742_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75);
lean_inc_ref(v_a_1424_);
v___x_1743_ = lean_apply_3(v_mkLogExceptionsTerm_1416_, v___x_1742_, v_a_1424_, v_a_1740_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1841_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_a_1745_ = lean_ctor_get(v___x_1743_, 1);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1747_ = v___x_1743_;
v_isShared_1748_ = v_isSharedCheck_1841_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1841_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v_quotContext_1749_; lean_object* v_currMacroScope_1750_; lean_object* v_ref_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; 
v_quotContext_1749_ = lean_ctor_get(v_a_1424_, 1);
v_currMacroScope_1750_ = lean_ctor_get(v_a_1424_, 2);
v_ref_1751_ = lean_ctor_get(v_a_1424_, 5);
v___x_1752_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78);
v___x_1753_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81);
v___x_1754_ = 0;
v___x_1755_ = l_Lean_SourceInfo_fromRef(v_ref_1751_, v___x_1754_);
v___x_1756_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83));
v___x_1757_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85);
v___x_1758_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86));
v___x_1759_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88));
lean_inc_n(v_currMacroScope_1750_, 2);
lean_inc_n(v_quotContext_1749_, 2);
v___x_1760_ = l_Lean_addMacroScope(v_quotContext_1749_, v___x_1759_, v_currMacroScope_1750_);
v___x_1761_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5));
v___x_1762_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6));
v___x_1763_ = lean_box(0);
v___x_1764_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91));
lean_inc_n(v___x_1755_, 3);
v___x_1765_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1755_);
lean_ctor_set(v___x_1765_, 1, v___x_1757_);
lean_ctor_set(v___x_1765_, 2, v___x_1760_);
lean_ctor_set(v___x_1765_, 3, v___x_1764_);
v___x_1766_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5));
v___x_1767_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93);
v___x_1768_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94));
v___x_1769_ = l_Lean_addMacroScope(v_quotContext_1749_, v___x_1768_, v_currMacroScope_1750_);
lean_inc(v___x_1769_);
v___x_1770_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1755_);
lean_ctor_set(v___x_1770_, 1, v___x_1767_);
lean_ctor_set(v___x_1770_, 2, v___x_1769_);
lean_ctor_set(v___x_1770_, 3, v___x_1763_);
v___x_1771_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96));
v___x_1772_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97));
if (v_isShared_1748_ == 0)
{
lean_ctor_set_tag(v___x_1747_, 2);
lean_ctor_set(v___x_1747_, 1, v___x_1772_);
lean_ctor_set(v___x_1747_, 0, v___x_1755_);
v___x_1774_ = v___x_1747_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1775_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99);
v___x_1776_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100));
lean_inc_n(v_currMacroScope_1750_, 2);
lean_inc_n(v_quotContext_1749_, 2);
v___x_1777_ = l_Lean_addMacroScope(v_quotContext_1749_, v___x_1776_, v_currMacroScope_1750_);
lean_inc(v___x_1777_);
lean_inc_n(v___x_1755_, 7);
v___x_1778_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1755_);
lean_ctor_set(v___x_1778_, 1, v___x_1775_);
lean_ctor_set(v___x_1778_, 2, v___x_1777_);
lean_ctor_set(v___x_1778_, 3, v___x_1763_);
v___x_1779_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101));
v___x_1780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1755_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102));
v___x_1782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1755_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
lean_inc_ref(v___x_1782_);
lean_inc_ref(v___x_1780_);
lean_inc_ref(v___x_1778_);
lean_inc_ref(v___x_1774_);
v___x_1783_ = l_Lean_Syntax_node5(v___x_1755_, v___x_1771_, v___x_1774_, v___x_1778_, v___x_1780_, v___x_1778_, v___x_1782_);
v___x_1784_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103);
v___x_1785_ = l_Lean_addMacroScope(v_quotContext_1749_, v___x_1741_, v_currMacroScope_1750_);
v___x_1786_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1755_);
lean_ctor_set(v___x_1786_, 1, v___x_1784_);
lean_ctor_set(v___x_1786_, 2, v___x_1785_);
lean_ctor_set(v___x_1786_, 3, v___x_1763_);
v___x_1787_ = l_Lean_Syntax_node5(v___x_1755_, v___x_1771_, v___x_1774_, v___x_1786_, v___x_1780_, v_a_1744_, v___x_1782_);
v___x_1788_ = l_Lean_Syntax_node5(v___x_1755_, v___x_1766_, v___x_1770_, v___x_1753_, v___x_1752_, v___x_1783_, v___x_1787_);
v___x_1789_ = l_Lean_Syntax_node2(v___x_1755_, v___x_1756_, v___x_1765_, v___x_1788_);
lean_inc_ref(v_a_1424_);
v___x_1790_ = lean_apply_3(v_mkMonadAdapt_1414_, v___x_1789_, v_a_1424_, v_a_1745_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1839_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_a_1792_ = lean_ctor_get(v___x_1790_, 1);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1794_ = v___x_1790_;
v_isShared_1795_ = v_isSharedCheck_1839_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1839_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v_fnName_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v_ref_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1796_ = l_Lean_TSyntax_getId(v_elabName_1420_);
v___x_1797_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105));
v___x_1798_ = l_Lean_Name_append(v___x_1796_, v___x_1797_);
v_fnName_1799_ = l_Lean_mkIdentFrom(v_elabName_1420_, v___x_1798_, v___x_1754_);
v___x_1800_ = lean_unsigned_to_nat(3u);
v___x_1801_ = lean_mk_empty_array_with_capacity(v___x_1800_);
v___x_1802_ = lean_array_push(v___x_1801_, v_tk_1419_);
lean_inc(v_elabName_1420_);
v___x_1803_ = lean_array_push(v___x_1802_, v_elabName_1420_);
lean_inc(v_type_1421_);
v___x_1804_ = lean_array_push(v___x_1803_, v_type_1421_);
v___x_1805_ = lean_box(2);
v___x_1806_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v___x_1766_);
lean_ctor_set(v___x_1806_, 2, v___x_1804_);
v_ref_1807_ = l_Lean_replaceRef(v___x_1806_, v_ref_1751_);
lean_dec_ref_known(v___x_1806_, 3);
v___x_1808_ = l_Lean_SourceInfo_fromRef(v_ref_1807_, v___x_1754_);
lean_dec(v_ref_1807_);
v___x_1809_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1));
v___x_1810_ = lean_obj_once(&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6, &l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6_once, _init_l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6);
lean_inc_n(v___x_1808_, 2);
v___x_1811_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1808_);
lean_ctor_set(v___x_1811_, 1, v___x_1766_);
lean_ctor_set(v___x_1811_, 2, v___x_1810_);
v___x_1812_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2));
v___x_1813_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106));
v___x_1814_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107));
if (v_isShared_1795_ == 0)
{
lean_ctor_set_tag(v___x_1794_, 2);
lean_ctor_set(v___x_1794_, 1, v___x_1813_);
lean_ctor_set(v___x_1794_, 0, v___x_1808_);
v___x_1816_ = v___x_1794_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v___x_1813_);
v___x_1816_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; size_t v_sz_1828_; size_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_inc_n(v___x_1808_, 9);
v___x_1817_ = l_Lean_Syntax_node1(v___x_1808_, v___x_1814_, v___x_1816_);
v___x_1818_ = l_Lean_Syntax_node1(v___x_1808_, v___x_1766_, v___x_1817_);
v___x_1819_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
v___x_1820_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108));
v___x_1821_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109));
v___x_1822_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1808_);
lean_ctor_set(v___x_1822_, 1, v___x_1820_);
v___x_1823_ = l_Lean_Syntax_node1(v___x_1808_, v___x_1821_, v___x_1822_);
v___x_1824_ = l_Lean_Syntax_node1(v___x_1808_, v___x_1766_, v___x_1823_);
v___x_1825_ = l_Lean_Syntax_node1(v___x_1808_, v___x_1819_, v___x_1824_);
v___x_1826_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110));
v___x_1827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1808_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v_sz_1828_ = lean_array_size(v_binders_1422_);
v___x_1829_ = ((size_t)0ULL);
lean_inc_ref(v_binders_1422_);
v___x_1830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_1828_, v___x_1829_, v_binders_1422_);
v___x_1831_ = l_Array_append___redArg(v___x_1810_, v___x_1830_);
lean_dec_ref(v___x_1830_);
v___x_1832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1808_);
lean_ctor_set(v___x_1832_, 1, v___x_1766_);
lean_ctor_set(v___x_1832_, 2, v___x_1831_);
v___x_1833_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__111));
v___x_1834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1808_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
if (lean_obj_tag(v_entries_x3f_1423_) == 1)
{
lean_object* v_val_1835_; lean_object* v___x_1836_; 
v_val_1835_ = lean_ctor_get(v_entries_x3f_1423_, 0);
lean_inc(v_val_1835_);
lean_dec_ref_known(v_entries_x3f_1423_, 1);
v___x_1836_ = l_Array_mkArray1___redArg(v_val_1835_);
lean_inc(v_quotContext_1749_);
lean_inc(v_currMacroScope_1750_);
v___y_1679_ = v___x_1808_;
v___y_1680_ = v___x_1777_;
v___y_1681_ = v___x_1811_;
v___y_1682_ = v_a_1792_;
v___y_1683_ = v___x_1810_;
v___y_1684_ = v___x_1809_;
v___y_1685_ = v___x_1827_;
v___y_1686_ = v___x_1769_;
v___y_1687_ = v___x_1756_;
v___y_1688_ = v___x_1752_;
v___y_1689_ = v___x_1812_;
v___y_1690_ = v_currMacroScope_1750_;
v___y_1691_ = v___x_1762_;
v___y_1692_ = v___x_1779_;
v___y_1693_ = v___x_1825_;
v___y_1694_ = v_sz_1828_;
v___y_1695_ = v___x_1767_;
v___y_1696_ = v___x_1758_;
v___y_1697_ = v___x_1834_;
v___y_1698_ = v___x_1781_;
v___y_1699_ = v_a_1739_;
v___y_1700_ = v___x_1775_;
v___y_1701_ = v_fnName_1799_;
v___y_1702_ = v___x_1772_;
v___y_1703_ = v___x_1763_;
v___y_1704_ = v___x_1805_;
v___y_1705_ = v___x_1771_;
v___y_1706_ = v_a_1791_;
v___y_1707_ = v___x_1829_;
v___y_1708_ = v___x_1753_;
v___y_1709_ = v___x_1832_;
v___y_1710_ = v_quotContext_1749_;
v___y_1711_ = v___x_1766_;
v___y_1712_ = v___x_1763_;
v___y_1713_ = v___x_1742_;
v___y_1714_ = v___x_1761_;
v___y_1715_ = v___x_1818_;
v___y_1716_ = v___x_1836_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1837_; 
lean_dec(v_entries_x3f_1423_);
v___x_1837_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
lean_inc(v_quotContext_1749_);
lean_inc(v_currMacroScope_1750_);
v___y_1679_ = v___x_1808_;
v___y_1680_ = v___x_1777_;
v___y_1681_ = v___x_1811_;
v___y_1682_ = v_a_1792_;
v___y_1683_ = v___x_1810_;
v___y_1684_ = v___x_1809_;
v___y_1685_ = v___x_1827_;
v___y_1686_ = v___x_1769_;
v___y_1687_ = v___x_1756_;
v___y_1688_ = v___x_1752_;
v___y_1689_ = v___x_1812_;
v___y_1690_ = v_currMacroScope_1750_;
v___y_1691_ = v___x_1762_;
v___y_1692_ = v___x_1779_;
v___y_1693_ = v___x_1825_;
v___y_1694_ = v_sz_1828_;
v___y_1695_ = v___x_1767_;
v___y_1696_ = v___x_1758_;
v___y_1697_ = v___x_1834_;
v___y_1698_ = v___x_1781_;
v___y_1699_ = v_a_1739_;
v___y_1700_ = v___x_1775_;
v___y_1701_ = v_fnName_1799_;
v___y_1702_ = v___x_1772_;
v___y_1703_ = v___x_1763_;
v___y_1704_ = v___x_1805_;
v___y_1705_ = v___x_1771_;
v___y_1706_ = v_a_1791_;
v___y_1707_ = v___x_1829_;
v___y_1708_ = v___x_1753_;
v___y_1709_ = v___x_1832_;
v___y_1710_ = v_quotContext_1749_;
v___y_1711_ = v___x_1766_;
v___y_1712_ = v___x_1763_;
v___y_1713_ = v___x_1742_;
v___y_1714_ = v___x_1761_;
v___y_1715_ = v___x_1818_;
v___y_1716_ = v___x_1837_;
goto v___jp_1678_;
}
}
}
}
else
{
lean_dec(v___x_1777_);
lean_dec(v___x_1769_);
lean_dec_ref(v_a_1739_);
lean_dec(v_entries_x3f_1423_);
lean_dec_ref(v_binders_1422_);
lean_dec(v_type_1421_);
lean_dec(v_elabName_1420_);
lean_dec(v_tk_1419_);
lean_dec(v_vis_x3f_1418_);
lean_dec(v_doc_x3f_1417_);
lean_dec(v_logExceptionsDefault_1415_);
lean_dec(v_monad_1413_);
return v___x_1790_;
}
}
}
}
else
{
lean_dec_ref(v_a_1739_);
lean_dec(v_entries_x3f_1423_);
lean_dec_ref(v_binders_1422_);
lean_dec(v_type_1421_);
lean_dec(v_elabName_1420_);
lean_dec(v_tk_1419_);
lean_dec(v_vis_x3f_1418_);
lean_dec(v_doc_x3f_1417_);
lean_dec(v_logExceptionsDefault_1415_);
lean_dec_ref(v_mkMonadAdapt_1414_);
lean_dec(v_monad_1413_);
return v___x_1743_;
}
}
v___jp_1842_:
{
if (lean_obj_tag(v___y_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v_a_1845_; 
v_a_1844_ = lean_ctor_get(v___y_1843_, 0);
lean_inc(v_a_1844_);
v_a_1845_ = lean_ctor_get(v___y_1843_, 1);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___y_1843_, 2);
v_a_1739_ = v_a_1844_;
v_a_1740_ = v_a_1845_;
goto v___jp_1738_;
}
else
{
lean_object* v_a_1846_; lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_entries_x3f_1423_);
lean_dec_ref(v_binders_1422_);
lean_dec(v_type_1421_);
lean_dec(v_elabName_1420_);
lean_dec(v_tk_1419_);
lean_dec(v_vis_x3f_1418_);
lean_dec(v_doc_x3f_1417_);
lean_dec_ref(v_mkLogExceptionsTerm_1416_);
lean_dec(v_logExceptionsDefault_1415_);
lean_dec_ref(v_mkMonadAdapt_1414_);
lean_dec(v_monad_1413_);
v_a_1846_ = lean_ctor_get(v___y_1843_, 0);
v_a_1847_ = lean_ctor_get(v___y_1843_, 1);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___y_1843_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___y_1843_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_inc(v_a_1846_);
lean_dec(v___y_1843_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1846_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___boxed(lean_object* v_monad_1864_, lean_object* v_mkMonadAdapt_1865_, lean_object* v_logExceptionsDefault_1866_, lean_object* v_mkLogExceptionsTerm_1867_, lean_object* v_doc_x3f_1868_, lean_object* v_vis_x3f_1869_, lean_object* v_tk_1870_, lean_object* v_elabName_1871_, lean_object* v_type_1872_, lean_object* v_binders_1873_, lean_object* v_entries_x3f_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v_monad_1864_, v_mkMonadAdapt_1865_, v_logExceptionsDefault_1866_, v_mkLogExceptionsTerm_1867_, v_doc_x3f_1868_, v_vis_x3f_1869_, v_tk_1870_, v_elabName_1871_, v_type_1872_, v_binders_1873_, v_entries_x3f_1874_, v_a_1875_, v_a_1876_);
lean_dec_ref(v_a_1875_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0(lean_object* v_logExceptions_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_logExceptions_1878_);
lean_ctor_set(v___x_1881_, 1, v___y_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0___boxed(lean_object* v_logExceptions_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0(v_logExceptions_1882_, v___y_1883_, v___y_1884_);
lean_dec_ref(v___y_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1(lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___y_1886_);
lean_ctor_set(v___x_1889_, 1, v___y_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1___boxed(lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1(v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec_ref(v___y_1891_);
return v_res_1893_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6));
v___x_1909_ = l_Lean_mkCIdent(v___x_1908_);
return v___x_1909_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9));
v___x_1915_ = l_Lean_mkCIdent(v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab(lean_object* v_x_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1));
lean_inc(v_x_1916_);
v___x_1920_ = l_Lean_Syntax_isOfKind(v_x_1916_, v___x_1919_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; 
lean_dec(v_x_1916_);
v___x_1921_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1918_);
return v___x_1921_;
}
else
{
lean_object* v___f_1922_; lean_object* v___f_1923_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v_entries_x3f_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___x_1967_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v_vis_x3f_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v_doc_x3f_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v___f_1922_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2));
v___f_1923_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3));
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_2009_ = l_Lean_Syntax_getArg(v_x_1916_, v___x_1967_);
v___x_2010_ = l_Lean_Syntax_isNone(v___x_2009_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2009_);
v___x_2012_ = l_Lean_Syntax_matchesNull(v___x_2009_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; 
lean_dec(v___x_2009_);
lean_dec(v_x_1916_);
v___x_2013_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1918_);
return v___x_2013_;
}
else
{
lean_object* v_doc_x3f_2014_; 
v_doc_x3f_2014_ = l_Lean_Syntax_getArg(v___x_2009_, v___x_1967_);
lean_dec(v___x_2009_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_2014_);
v___x_2018_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2014_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; 
lean_dec(v_doc_x3f_2014_);
lean_dec(v_x_1916_);
v___x_2019_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1918_);
return v___x_2019_;
}
else
{
goto v___jp_2015_;
}
}
else
{
goto v___jp_2015_;
}
v___jp_2015_:
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v_doc_x3f_2014_);
v_doc_x3f_1998_ = v___x_2016_;
v___y_1999_ = v_a_1917_;
v___y_2000_ = v_a_1918_;
goto v___jp_1997_;
}
}
}
else
{
lean_object* v___x_2020_; 
lean_dec(v___x_2009_);
v___x_2020_ = lean_box(0);
v_doc_x3f_1998_ = v___x_2020_;
v___y_1999_ = v_a_1917_;
v___y_2000_ = v_a_1918_;
goto v___jp_1997_;
}
v___jp_1924_:
{
lean_object* v_binders_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_binders_1934_ = l_Lean_Syntax_getArgs(v___y_1930_);
lean_dec(v___y_1930_);
v___x_1935_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7, &l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7_once, _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7);
v___x_1936_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10, &l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10_once, _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10);
v___x_1937_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_1935_, v___f_1923_, v___x_1936_, v___f_1922_, v___y_1928_, v___y_1929_, v___y_1925_, v___y_1926_, v___y_1927_, v_binders_1934_, v_entries_x3f_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_a_1939_ = lean_ctor_get(v___x_1937_, 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1937_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1938_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v_a_1947_ = lean_ctor_get(v___x_1937_, 0);
v_a_1948_ = lean_ctor_get(v___x_1937_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1937_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_inc(v_a_1947_);
lean_dec(v___x_1937_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1947_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
v___jp_1956_:
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___y_1965_);
v___y_1925_ = v___y_1957_;
v___y_1926_ = v___y_1959_;
v___y_1927_ = v___y_1960_;
v___y_1928_ = v___y_1961_;
v___y_1929_ = v___y_1963_;
v___y_1930_ = v___y_1962_;
v_entries_x3f_1931_ = v___x_1966_;
v___y_1932_ = v___y_1964_;
v___y_1933_ = v___y_1958_;
goto v___jp_1924_;
}
v___jp_1968_:
{
lean_object* v___x_1974_; lean_object* v_elabName_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1974_ = lean_unsigned_to_nat(3u);
v_elabName_1975_ = l_Lean_Syntax_getArg(v_x_1916_, v___x_1974_);
v___x_1976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_elabName_1975_);
v___x_1977_ = l_Lean_Syntax_isOfKind(v_elabName_1975_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec(v_elabName_1975_);
lean_dec(v_vis_x3f_1971_);
lean_dec(v___y_1970_);
lean_dec(v_x_1916_);
v___x_1978_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1973_);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v_type_1980_; uint8_t v___x_1981_; 
v___x_1979_ = lean_unsigned_to_nat(4u);
v_type_1980_ = l_Lean_Syntax_getArg(v_x_1916_, v___x_1979_);
lean_inc(v_type_1980_);
v___x_1981_ = l_Lean_Syntax_isOfKind(v_type_1980_, v___x_1976_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; 
lean_dec(v_type_1980_);
lean_dec(v_elabName_1975_);
lean_dec(v_vis_x3f_1971_);
lean_dec(v___y_1970_);
lean_dec(v_x_1916_);
v___x_1982_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1973_);
return v___x_1982_;
}
else
{
lean_object* v___x_1983_; lean_object* v_tk_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1983_ = lean_unsigned_to_nat(2u);
v_tk_1984_ = l_Lean_Syntax_getArg(v_x_1916_, v___x_1983_);
v___x_1985_ = lean_unsigned_to_nat(5u);
v___x_1986_ = l_Lean_Syntax_getArg(v_x_1916_, v___x_1985_);
v___x_1987_ = lean_unsigned_to_nat(6u);
v___x_1988_ = l_Lean_Syntax_getArg(v_x_1916_, v___x_1987_);
lean_dec(v_x_1916_);
v___x_1989_ = l_Lean_Syntax_isNone(v___x_1988_);
if (v___x_1989_ == 0)
{
uint8_t v___x_1990_; 
lean_inc(v___x_1988_);
v___x_1990_ = l_Lean_Syntax_matchesNull(v___x_1988_, v___y_1969_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; 
lean_dec(v___x_1988_);
lean_dec(v___x_1986_);
lean_dec(v_tk_1984_);
lean_dec(v_type_1980_);
lean_dec(v_elabName_1975_);
lean_dec(v_vis_x3f_1971_);
lean_dec(v___y_1970_);
v___x_1991_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1973_);
return v___x_1991_;
}
else
{
lean_object* v_entries_x3f_1992_; 
v_entries_x3f_1992_ = l_Lean_Syntax_getArg(v___x_1988_, v___x_1967_);
lean_dec(v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1993_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_1992_);
v___x_1994_ = l_Lean_Syntax_isOfKind(v_entries_x3f_1992_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; 
lean_dec(v_entries_x3f_1992_);
lean_dec(v___x_1986_);
lean_dec(v_tk_1984_);
lean_dec(v_type_1980_);
lean_dec(v_elabName_1975_);
lean_dec(v_vis_x3f_1971_);
lean_dec(v___y_1970_);
v___x_1995_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1973_);
return v___x_1995_;
}
else
{
v___y_1957_ = v_tk_1984_;
v___y_1958_ = v___y_1973_;
v___y_1959_ = v_elabName_1975_;
v___y_1960_ = v_type_1980_;
v___y_1961_ = v___y_1970_;
v___y_1962_ = v___x_1986_;
v___y_1963_ = v_vis_x3f_1971_;
v___y_1964_ = v___y_1972_;
v___y_1965_ = v_entries_x3f_1992_;
goto v___jp_1956_;
}
}
else
{
v___y_1957_ = v_tk_1984_;
v___y_1958_ = v___y_1973_;
v___y_1959_ = v_elabName_1975_;
v___y_1960_ = v_type_1980_;
v___y_1961_ = v___y_1970_;
v___y_1962_ = v___x_1986_;
v___y_1963_ = v_vis_x3f_1971_;
v___y_1964_ = v___y_1972_;
v___y_1965_ = v_entries_x3f_1992_;
goto v___jp_1956_;
}
}
}
else
{
lean_object* v___x_1996_; 
lean_dec(v___x_1988_);
v___x_1996_ = lean_box(0);
v___y_1925_ = v_tk_1984_;
v___y_1926_ = v_elabName_1975_;
v___y_1927_ = v_type_1980_;
v___y_1928_ = v___y_1970_;
v___y_1929_ = v_vis_x3f_1971_;
v___y_1930_ = v___x_1986_;
v_entries_x3f_1931_ = v___x_1996_;
v___y_1932_ = v___y_1972_;
v___y_1933_ = v___y_1973_;
goto v___jp_1924_;
}
}
}
}
v___jp_1997_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2001_ = lean_unsigned_to_nat(1u);
v___x_2002_ = l_Lean_Syntax_getArg(v_x_1916_, v___x_2001_);
v___x_2003_ = l_Lean_Syntax_isNone(v___x_2002_);
if (v___x_2003_ == 0)
{
uint8_t v___x_2004_; 
lean_inc(v___x_2002_);
v___x_2004_ = l_Lean_Syntax_matchesNull(v___x_2002_, v___x_2001_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; 
lean_dec(v___x_2002_);
lean_dec(v_doc_x3f_1998_);
lean_dec(v_x_1916_);
v___x_2005_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2000_);
return v___x_2005_;
}
else
{
lean_object* v_vis_x3f_2006_; lean_object* v___x_2007_; 
v_vis_x3f_2006_ = l_Lean_Syntax_getArg(v___x_2002_, v___x_1967_);
lean_dec(v___x_2002_);
v___x_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2007_, 0, v_vis_x3f_2006_);
v___y_1969_ = v___x_2001_;
v___y_1970_ = v_doc_x3f_1998_;
v_vis_x3f_1971_ = v___x_2007_;
v___y_1972_ = v___y_1999_;
v___y_1973_ = v___y_2000_;
goto v___jp_1968_;
}
}
else
{
lean_object* v___x_2008_; 
lean_dec(v___x_2002_);
v___x_2008_ = lean_box(0);
v___y_1969_ = v___x_2001_;
v___y_1970_ = v_doc_x3f_1998_;
v_vis_x3f_1971_ = v___x_2008_;
v___y_1972_ = v___y_1999_;
v___y_1973_ = v___y_2000_;
goto v___jp_1968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___boxed(lean_object* v_x_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab(v_x_2021_, v_a_2022_, v_a_2023_);
lean_dec_ref(v_a_2022_);
return v_res_2024_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1(){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2032_ = l_Lean_Elab_macroAttribute;
v___x_2033_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1));
v___x_2034_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1));
v___x_2035_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___boxed), 3, 0);
v___x_2036_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2032_, v___x_2033_, v___x_2034_, v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2037_;
v_res_2037_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1();
stack->m_obj
 = v_res_2037_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___boxed(lean_object* v_a_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1();
return v_res_2039_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab(lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_2045_ = lean_unsigned_to_nat(2u);
v___x_2046_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_2044_, v___x_2045_, v_a_2040_, v_a_2041_, v_a_2042_);
return v___x_2046_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2040_ = stack[0].m_obj;
lean_object* v_a_2041_ = stack[1].m_obj;
lean_object* v_a_2042_ = stack[2].m_obj;
lean_object* v_res_2047_;
v_res_2047_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab(v_a_2040_, v_a_2041_, v_a_2042_);
stack->m_obj
 = v_res_2047_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___boxed(lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab(v_a_2048_, v_a_2049_, v_a_2050_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_a_2048_);
return v_res_2052_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___boxed), 4, 0);
v___x_2054_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_2054_, 0, v___x_2053_);
return v___x_2054_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1(){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1));
v___x_2057_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0);
v___x_2058_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_2056_, v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2059_;
v_res_2059_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1();
stack->m_obj
 = v_res_2059_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___boxed(lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1();
return v_res_2061_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__8));
v___x_2074_ = l_String_toRawSubstring_x27(v___x_2073_);
return v___x_2074_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13));
v___x_2080_ = l_String_toRawSubstring_x27(v___x_2079_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__21));
v___x_2096_ = l_String_toRawSubstring_x27(v___x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1(lean_object* v___x_2099_, lean_object* v___x_2100_, lean_object* v___x_2101_, lean_object* v___x_2102_, lean_object* v___x_2103_, lean_object* v_logExceptions_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_quotContext_2107_; lean_object* v_currMacroScope_2108_; lean_object* v_ref_2109_; uint8_t v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_quotContext_2107_ = lean_ctor_get(v___y_2105_, 1);
v_currMacroScope_2108_ = lean_ctor_get(v___y_2105_, 2);
v_ref_2109_ = lean_ctor_get(v___y_2105_, 5);
v___x_2110_ = 0;
v___x_2111_ = l_Lean_SourceInfo_fromRef(v_ref_2109_, v___x_2110_);
v___x_2112_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1));
v___x_2113_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2));
lean_inc_n(v___x_2111_, 14);
v___x_2114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2111_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3));
lean_inc_ref_n(v___x_2101_, 5);
lean_inc_ref_n(v___x_2100_, 4);
lean_inc_ref_n(v___x_2099_, 9);
v___x_2116_ = l_Lean_Name_mkStr4(v___x_2099_, v___x_2100_, v___x_2101_, v___x_2115_);
v___x_2117_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4));
v___x_2118_ = l_Lean_Name_mkStr4(v___x_2099_, v___x_2100_, v___x_2101_, v___x_2117_);
v___x_2119_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5));
v___x_2120_ = l_Lean_Name_mkStr4(v___x_2099_, v___x_2100_, v___x_2101_, v___x_2119_);
v___x_2121_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97));
v___x_2122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2111_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7));
v___x_2124_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9);
v___x_2125_ = lean_box(0);
lean_inc_n(v_currMacroScope_2108_, 3);
lean_inc_n(v_quotContext_2107_, 3);
v___x_2126_ = l_Lean_addMacroScope(v_quotContext_2107_, v___x_2125_, v_currMacroScope_2108_);
lean_inc_ref_n(v___x_2102_, 2);
v___x_2127_ = l_Lean_Name_mkStr3(v___x_2099_, v___x_2102_, v___x_2103_);
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
v___x_2129_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10));
v___x_2130_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2));
v___x_2131_ = l_Lean_Name_mkStr3(v___x_2099_, v___x_2129_, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
v___x_2133_ = l_Lean_Name_mkStr3(v___x_2099_, v___x_2102_, v___x_2130_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
v___x_2135_ = l_Lean_Name_mkStr3(v___x_2099_, v___x_2102_, v___x_2101_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
v___x_2137_ = l_Lean_Name_mkStr2(v___x_2099_, v___x_2129_);
v___x_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
v___x_2139_ = lean_box(0);
v___x_2140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2138_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2136_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2134_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2132_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2128_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2111_);
lean_ctor_set(v___x_2145_, 1, v___x_2124_);
lean_ctor_set(v___x_2145_, 2, v___x_2126_);
lean_ctor_set(v___x_2145_, 3, v___x_2144_);
v___x_2146_ = l_Lean_Syntax_node1(v___x_2111_, v___x_2123_, v___x_2145_);
v___x_2147_ = l_Lean_Syntax_node2(v___x_2111_, v___x_2120_, v___x_2122_, v___x_2146_);
v___x_2148_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11));
v___x_2149_ = l_Lean_Name_mkStr4(v___x_2099_, v___x_2100_, v___x_2101_, v___x_2148_);
v___x_2150_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12));
v___x_2151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2111_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66));
v___x_2153_ = l_Lean_Name_mkStr4(v___x_2099_, v___x_2100_, v___x_2101_, v___x_2152_);
v___x_2154_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14);
v___x_2155_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15));
v___x_2156_ = l_Lean_addMacroScope(v_quotContext_2107_, v___x_2155_, v_currMacroScope_2108_);
v___x_2157_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19));
v___x_2158_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2111_);
lean_ctor_set(v___x_2158_, 1, v___x_2154_);
lean_ctor_set(v___x_2158_, 2, v___x_2156_);
lean_ctor_set(v___x_2158_, 3, v___x_2157_);
v___x_2159_ = l_Lean_Syntax_node1(v___x_2111_, v___x_2153_, v___x_2158_);
v___x_2160_ = l_Lean_Syntax_node2(v___x_2111_, v___x_2149_, v___x_2151_, v___x_2159_);
v___x_2161_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102));
v___x_2162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2111_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = l_Lean_Syntax_node3(v___x_2111_, v___x_2118_, v___x_2147_, v___x_2160_, v___x_2162_);
v___x_2164_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20));
v___x_2165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2111_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22);
v___x_2167_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__23));
v___x_2168_ = l_Lean_addMacroScope(v_quotContext_2107_, v___x_2167_, v_currMacroScope_2108_);
v___x_2169_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2111_);
lean_ctor_set(v___x_2169_, 1, v___x_2166_);
lean_ctor_set(v___x_2169_, 2, v___x_2168_);
lean_ctor_set(v___x_2169_, 3, v___x_2139_);
v___x_2170_ = l_Lean_Syntax_node3(v___x_2111_, v___x_2116_, v___x_2163_, v___x_2165_, v___x_2169_);
v___x_2171_ = l_Lean_Syntax_node3(v___x_2111_, v___x_2112_, v_logExceptions_2104_, v___x_2114_, v___x_2170_);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v___y_2106_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___boxed(lean_object* v___x_2173_, lean_object* v___x_2174_, lean_object* v___x_2175_, lean_object* v___x_2176_, lean_object* v___x_2177_, lean_object* v_logExceptions_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1(v___x_2173_, v___x_2174_, v___x_2175_, v___x_2176_, v___x_2177_, v_logExceptions_2178_, v___y_2179_, v___y_2180_);
lean_dec_ref(v___y_2179_);
return v_res_2181_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4));
v___x_2201_ = l_Lean_mkCIdent(v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7));
v___x_2207_ = l_Lean_mkCIdent(v___x_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab(lean_object* v_x_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1));
lean_inc(v_x_2208_);
v___x_2212_ = l_Lean_Syntax_isOfKind(v_x_2208_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; 
lean_dec(v_x_2208_);
v___x_2213_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2210_);
return v___x_2213_;
}
else
{
lean_object* v___f_2214_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v_entries_x3f_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___x_2259_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v_vis_x3f_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v_doc_x3f_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___f_2214_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3));
v___x_2259_ = lean_unsigned_to_nat(0u);
v___x_2301_ = l_Lean_Syntax_getArg(v_x_2208_, v___x_2259_);
v___x_2302_ = l_Lean_Syntax_isNone(v___x_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2303_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2301_);
v___x_2304_ = l_Lean_Syntax_matchesNull(v___x_2301_, v___x_2303_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; 
lean_dec(v___x_2301_);
lean_dec(v_x_2208_);
v___x_2305_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2210_);
return v___x_2305_;
}
else
{
lean_object* v_doc_x3f_2306_; 
v_doc_x3f_2306_ = l_Lean_Syntax_getArg(v___x_2301_, v___x_2259_);
lean_dec(v___x_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2309_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_2306_);
v___x_2310_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2306_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; 
lean_dec(v_doc_x3f_2306_);
lean_dec(v_x_2208_);
v___x_2311_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2210_);
return v___x_2311_;
}
else
{
goto v___jp_2307_;
}
}
else
{
goto v___jp_2307_;
}
v___jp_2307_:
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2308_, 0, v_doc_x3f_2306_);
v_doc_x3f_2290_ = v___x_2308_;
v___y_2291_ = v_a_2209_;
v___y_2292_ = v_a_2210_;
goto v___jp_2289_;
}
}
}
else
{
lean_object* v___x_2312_; 
lean_dec(v___x_2301_);
v___x_2312_ = lean_box(0);
v_doc_x3f_2290_ = v___x_2312_;
v___y_2291_ = v_a_2209_;
v___y_2292_ = v_a_2210_;
goto v___jp_2289_;
}
v___jp_2215_:
{
lean_object* v___f_2225_; lean_object* v_binders_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___f_2225_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2));
v_binders_2226_ = l_Lean_Syntax_getArgs(v___y_2221_);
lean_dec(v___y_2221_);
v___x_2227_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5);
v___x_2228_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8);
v___x_2229_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_2227_, v___f_2214_, v___x_2228_, v___f_2225_, v___y_2216_, v___y_2220_, v___y_2218_, v___y_2219_, v___y_2217_, v_binders_2226_, v_entries_x3f_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_a_2231_ = lean_ctor_get(v___x_2229_, 1);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2229_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2230_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
v_a_2239_ = lean_ctor_get(v___x_2229_, 0);
v_a_2240_ = lean_ctor_get(v___x_2229_, 1);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2229_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_inc(v_a_2239_);
lean_dec(v___x_2229_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2239_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
v___jp_2248_:
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___y_2256_);
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___y_2253_;
v___y_2218_ = v___y_2252_;
v___y_2219_ = v___y_2254_;
v___y_2220_ = v___y_2255_;
v___y_2221_ = v___y_2257_;
v_entries_x3f_2222_ = v___x_2258_;
v___y_2223_ = v___y_2251_;
v___y_2224_ = v___y_2250_;
goto v___jp_2215_;
}
v___jp_2260_:
{
lean_object* v___x_2266_; lean_object* v_elabName_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2266_ = lean_unsigned_to_nat(3u);
v_elabName_2267_ = l_Lean_Syntax_getArg(v_x_2208_, v___x_2266_);
v___x_2268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_elabName_2267_);
v___x_2269_ = l_Lean_Syntax_isOfKind(v_elabName_2267_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; 
lean_dec(v_elabName_2267_);
lean_dec(v_vis_x3f_2263_);
lean_dec(v___y_2261_);
lean_dec(v_x_2208_);
v___x_2270_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2265_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; lean_object* v_type_2272_; uint8_t v___x_2273_; 
v___x_2271_ = lean_unsigned_to_nat(4u);
v_type_2272_ = l_Lean_Syntax_getArg(v_x_2208_, v___x_2271_);
lean_inc(v_type_2272_);
v___x_2273_ = l_Lean_Syntax_isOfKind(v_type_2272_, v___x_2268_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; 
lean_dec(v_type_2272_);
lean_dec(v_elabName_2267_);
lean_dec(v_vis_x3f_2263_);
lean_dec(v___y_2261_);
lean_dec(v_x_2208_);
v___x_2274_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2265_);
return v___x_2274_;
}
else
{
lean_object* v___x_2275_; lean_object* v_tk_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v___x_2275_ = lean_unsigned_to_nat(2u);
v_tk_2276_ = l_Lean_Syntax_getArg(v_x_2208_, v___x_2275_);
v___x_2277_ = lean_unsigned_to_nat(5u);
v___x_2278_ = l_Lean_Syntax_getArg(v_x_2208_, v___x_2277_);
v___x_2279_ = lean_unsigned_to_nat(6u);
v___x_2280_ = l_Lean_Syntax_getArg(v_x_2208_, v___x_2279_);
lean_dec(v_x_2208_);
v___x_2281_ = l_Lean_Syntax_isNone(v___x_2280_);
if (v___x_2281_ == 0)
{
uint8_t v___x_2282_; 
lean_inc(v___x_2280_);
v___x_2282_ = l_Lean_Syntax_matchesNull(v___x_2280_, v___y_2262_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; 
lean_dec(v___x_2280_);
lean_dec(v___x_2278_);
lean_dec(v_tk_2276_);
lean_dec(v_type_2272_);
lean_dec(v_elabName_2267_);
lean_dec(v_vis_x3f_2263_);
lean_dec(v___y_2261_);
v___x_2283_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2265_);
return v___x_2283_;
}
else
{
lean_object* v_entries_x3f_2284_; 
v_entries_x3f_2284_ = l_Lean_Syntax_getArg(v___x_2280_, v___x_2259_);
lean_dec(v___x_2280_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2285_; uint8_t v___x_2286_; 
v___x_2285_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_2284_);
v___x_2286_ = l_Lean_Syntax_isOfKind(v_entries_x3f_2284_, v___x_2285_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; 
lean_dec(v_entries_x3f_2284_);
lean_dec(v___x_2278_);
lean_dec(v_tk_2276_);
lean_dec(v_type_2272_);
lean_dec(v_elabName_2267_);
lean_dec(v_vis_x3f_2263_);
lean_dec(v___y_2261_);
v___x_2287_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2265_);
return v___x_2287_;
}
else
{
v___y_2249_ = v___y_2261_;
v___y_2250_ = v___y_2265_;
v___y_2251_ = v___y_2264_;
v___y_2252_ = v_tk_2276_;
v___y_2253_ = v_type_2272_;
v___y_2254_ = v_elabName_2267_;
v___y_2255_ = v_vis_x3f_2263_;
v___y_2256_ = v_entries_x3f_2284_;
v___y_2257_ = v___x_2278_;
goto v___jp_2248_;
}
}
else
{
v___y_2249_ = v___y_2261_;
v___y_2250_ = v___y_2265_;
v___y_2251_ = v___y_2264_;
v___y_2252_ = v_tk_2276_;
v___y_2253_ = v_type_2272_;
v___y_2254_ = v_elabName_2267_;
v___y_2255_ = v_vis_x3f_2263_;
v___y_2256_ = v_entries_x3f_2284_;
v___y_2257_ = v___x_2278_;
goto v___jp_2248_;
}
}
}
else
{
lean_object* v___x_2288_; 
lean_dec(v___x_2280_);
v___x_2288_ = lean_box(0);
v___y_2216_ = v___y_2261_;
v___y_2217_ = v_type_2272_;
v___y_2218_ = v_tk_2276_;
v___y_2219_ = v_elabName_2267_;
v___y_2220_ = v_vis_x3f_2263_;
v___y_2221_ = v___x_2278_;
v_entries_x3f_2222_ = v___x_2288_;
v___y_2223_ = v___y_2264_;
v___y_2224_ = v___y_2265_;
goto v___jp_2215_;
}
}
}
}
v___jp_2289_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2293_ = lean_unsigned_to_nat(1u);
v___x_2294_ = l_Lean_Syntax_getArg(v_x_2208_, v___x_2293_);
v___x_2295_ = l_Lean_Syntax_isNone(v___x_2294_);
if (v___x_2295_ == 0)
{
uint8_t v___x_2296_; 
lean_inc(v___x_2294_);
v___x_2296_ = l_Lean_Syntax_matchesNull(v___x_2294_, v___x_2293_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; 
lean_dec(v___x_2294_);
lean_dec(v_doc_x3f_2290_);
lean_dec(v_x_2208_);
v___x_2297_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2292_);
return v___x_2297_;
}
else
{
lean_object* v_vis_x3f_2298_; lean_object* v___x_2299_; 
v_vis_x3f_2298_ = l_Lean_Syntax_getArg(v___x_2294_, v___x_2259_);
lean_dec(v___x_2294_);
v___x_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2299_, 0, v_vis_x3f_2298_);
v___y_2261_ = v_doc_x3f_2290_;
v___y_2262_ = v___x_2293_;
v_vis_x3f_2263_ = v___x_2299_;
v___y_2264_ = v___y_2291_;
v___y_2265_ = v___y_2292_;
goto v___jp_2260_;
}
}
else
{
lean_object* v___x_2300_; 
lean_dec(v___x_2294_);
v___x_2300_ = lean_box(0);
v___y_2261_ = v_doc_x3f_2290_;
v___y_2262_ = v___x_2293_;
v_vis_x3f_2263_ = v___x_2300_;
v___y_2264_ = v___y_2291_;
v___y_2265_ = v___y_2292_;
goto v___jp_2260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___boxed(lean_object* v_x_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab(v_x_2313_, v_a_2314_, v_a_2315_);
lean_dec_ref(v_a_2314_);
return v_res_2316_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1(){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2324_ = l_Lean_Elab_macroAttribute;
v___x_2325_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1));
v___x_2326_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1));
v___x_2327_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___boxed), 3, 0);
v___x_2328_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2324_, v___x_2325_, v___x_2326_, v___x_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2329_;
v_res_2329_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1();
stack->m_obj
 = v_res_2329_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___boxed(lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1();
return v_res_2331_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab(lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2336_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_2337_ = lean_unsigned_to_nat(2u);
v___x_2338_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_2336_, v___x_2337_, v_a_2332_, v_a_2333_, v_a_2334_);
return v___x_2338_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2332_ = stack[0].m_obj;
lean_object* v_a_2333_ = stack[1].m_obj;
lean_object* v_a_2334_ = stack[2].m_obj;
lean_object* v_res_2339_;
v_res_2339_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab(v_a_2332_, v_a_2333_, v_a_2334_);
stack->m_obj
 = v_res_2339_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___boxed(lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab(v_a_2340_, v_a_2341_, v_a_2342_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
lean_dec(v_a_2340_);
return v_res_2344_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___boxed), 4, 0);
v___x_2346_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_2346_, 0, v___x_2345_);
return v___x_2346_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1(){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2348_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1));
v___x_2349_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0);
v___x_2350_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_2348_, v___x_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2351_;
v_res_2351_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1();
stack->m_obj
 = v_res_2351_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___boxed(lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1();
return v_res_2353_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__0));
v___x_2356_ = l_String_toRawSubstring_x27(v___x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1(lean_object* v___x_2359_, lean_object* v___x_2360_, lean_object* v___x_2361_, lean_object* v___x_2362_, lean_object* v___x_2363_, lean_object* v_logExceptions_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_quotContext_2367_; lean_object* v_currMacroScope_2368_; lean_object* v_ref_2369_; uint8_t v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_quotContext_2367_ = lean_ctor_get(v___y_2365_, 1);
v_currMacroScope_2368_ = lean_ctor_get(v___y_2365_, 2);
v_ref_2369_ = lean_ctor_get(v___y_2365_, 5);
v___x_2370_ = 0;
v___x_2371_ = l_Lean_SourceInfo_fromRef(v_ref_2369_, v___x_2370_);
v___x_2372_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1));
v___x_2373_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2));
lean_inc_n(v___x_2371_, 14);
v___x_2374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2371_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3));
lean_inc_ref_n(v___x_2361_, 5);
lean_inc_ref_n(v___x_2360_, 4);
lean_inc_ref_n(v___x_2359_, 9);
v___x_2376_ = l_Lean_Name_mkStr4(v___x_2359_, v___x_2360_, v___x_2361_, v___x_2375_);
v___x_2377_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4));
v___x_2378_ = l_Lean_Name_mkStr4(v___x_2359_, v___x_2360_, v___x_2361_, v___x_2377_);
v___x_2379_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5));
v___x_2380_ = l_Lean_Name_mkStr4(v___x_2359_, v___x_2360_, v___x_2361_, v___x_2379_);
v___x_2381_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97));
v___x_2382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2371_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7));
v___x_2384_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9);
v___x_2385_ = lean_box(0);
lean_inc_n(v_currMacroScope_2368_, 3);
lean_inc_n(v_quotContext_2367_, 3);
v___x_2386_ = l_Lean_addMacroScope(v_quotContext_2367_, v___x_2385_, v_currMacroScope_2368_);
lean_inc_ref_n(v___x_2362_, 2);
v___x_2387_ = l_Lean_Name_mkStr3(v___x_2359_, v___x_2362_, v___x_2363_);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
v___x_2389_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10));
v___x_2390_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2));
v___x_2391_ = l_Lean_Name_mkStr3(v___x_2359_, v___x_2389_, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
v___x_2393_ = l_Lean_Name_mkStr3(v___x_2359_, v___x_2362_, v___x_2390_);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
v___x_2395_ = l_Lean_Name_mkStr3(v___x_2359_, v___x_2362_, v___x_2361_);
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
v___x_2397_ = l_Lean_Name_mkStr2(v___x_2359_, v___x_2389_);
v___x_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
v___x_2399_ = lean_box(0);
v___x_2400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2396_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2394_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2392_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___x_2404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2388_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2371_);
lean_ctor_set(v___x_2405_, 1, v___x_2384_);
lean_ctor_set(v___x_2405_, 2, v___x_2386_);
lean_ctor_set(v___x_2405_, 3, v___x_2404_);
v___x_2406_ = l_Lean_Syntax_node1(v___x_2371_, v___x_2383_, v___x_2405_);
v___x_2407_ = l_Lean_Syntax_node2(v___x_2371_, v___x_2380_, v___x_2382_, v___x_2406_);
v___x_2408_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11));
v___x_2409_ = l_Lean_Name_mkStr4(v___x_2359_, v___x_2360_, v___x_2361_, v___x_2408_);
v___x_2410_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12));
v___x_2411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2371_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66));
v___x_2413_ = l_Lean_Name_mkStr4(v___x_2359_, v___x_2360_, v___x_2361_, v___x_2412_);
v___x_2414_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14);
v___x_2415_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15));
v___x_2416_ = l_Lean_addMacroScope(v_quotContext_2367_, v___x_2415_, v_currMacroScope_2368_);
v___x_2417_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19));
v___x_2418_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2371_);
lean_ctor_set(v___x_2418_, 1, v___x_2414_);
lean_ctor_set(v___x_2418_, 2, v___x_2416_);
lean_ctor_set(v___x_2418_, 3, v___x_2417_);
v___x_2419_ = l_Lean_Syntax_node1(v___x_2371_, v___x_2413_, v___x_2418_);
v___x_2420_ = l_Lean_Syntax_node2(v___x_2371_, v___x_2409_, v___x_2411_, v___x_2419_);
v___x_2421_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102));
v___x_2422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2371_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = l_Lean_Syntax_node3(v___x_2371_, v___x_2378_, v___x_2407_, v___x_2420_, v___x_2422_);
v___x_2424_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20));
v___x_2425_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2371_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1, &l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1);
v___x_2427_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__2));
v___x_2428_ = l_Lean_addMacroScope(v_quotContext_2367_, v___x_2427_, v_currMacroScope_2368_);
v___x_2429_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2371_);
lean_ctor_set(v___x_2429_, 1, v___x_2426_);
lean_ctor_set(v___x_2429_, 2, v___x_2428_);
lean_ctor_set(v___x_2429_, 3, v___x_2399_);
v___x_2430_ = l_Lean_Syntax_node3(v___x_2371_, v___x_2376_, v___x_2423_, v___x_2425_, v___x_2429_);
v___x_2431_ = l_Lean_Syntax_node3(v___x_2371_, v___x_2372_, v_logExceptions_2364_, v___x_2374_, v___x_2430_);
v___x_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
lean_ctor_set(v___x_2432_, 1, v___y_2366_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___boxed(lean_object* v___x_2433_, lean_object* v___x_2434_, lean_object* v___x_2435_, lean_object* v___x_2436_, lean_object* v___x_2437_, lean_object* v_logExceptions_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1(v___x_2433_, v___x_2434_, v___x_2435_, v___x_2436_, v___x_2437_, v_logExceptions_2438_, v___y_2439_, v___y_2440_);
lean_dec_ref(v___y_2439_);
return v_res_2441_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5));
v___x_2462_ = l_Lean_mkCIdent(v___x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig(lean_object* v_x_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1));
lean_inc(v_x_2463_);
v___x_2467_ = l_Lean_Syntax_isOfKind(v_x_2463_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
lean_dec(v_x_2463_);
v___x_2468_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2465_);
return v___x_2468_;
}
else
{
lean_object* v___f_2469_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v_entries_x3f_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___x_2514_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v_vis_x3f_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v_doc_x3f_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___f_2469_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3));
v___x_2514_ = lean_unsigned_to_nat(0u);
v___x_2556_ = l_Lean_Syntax_getArg(v_x_2463_, v___x_2514_);
v___x_2557_ = l_Lean_Syntax_isNone(v___x_2556_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2558_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2556_);
v___x_2559_ = l_Lean_Syntax_matchesNull(v___x_2556_, v___x_2558_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; 
lean_dec(v___x_2556_);
lean_dec(v_x_2463_);
v___x_2560_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2465_);
return v___x_2560_;
}
else
{
lean_object* v_doc_x3f_2561_; 
v_doc_x3f_2561_ = l_Lean_Syntax_getArg(v___x_2556_, v___x_2514_);
lean_dec(v___x_2556_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2564_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_2561_);
v___x_2565_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2561_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; 
lean_dec(v_doc_x3f_2561_);
lean_dec(v_x_2463_);
v___x_2566_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2465_);
return v___x_2566_;
}
else
{
goto v___jp_2562_;
}
}
else
{
goto v___jp_2562_;
}
v___jp_2562_:
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_doc_x3f_2561_);
v_doc_x3f_2545_ = v___x_2563_;
v___y_2546_ = v_a_2464_;
v___y_2547_ = v_a_2465_;
goto v___jp_2544_;
}
}
}
else
{
lean_object* v___x_2567_; 
lean_dec(v___x_2556_);
v___x_2567_ = lean_box(0);
v_doc_x3f_2545_ = v___x_2567_;
v___y_2546_ = v_a_2464_;
v___y_2547_ = v_a_2465_;
goto v___jp_2544_;
}
v___jp_2470_:
{
lean_object* v___f_2480_; lean_object* v_binders_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___f_2480_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2));
v_binders_2481_ = l_Lean_Syntax_getArgs(v___y_2475_);
lean_dec(v___y_2475_);
v___x_2482_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6, &l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6);
v___x_2483_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8);
v___x_2484_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_2482_, v___f_2469_, v___x_2483_, v___f_2480_, v___y_2474_, v___y_2476_, v___y_2472_, v___y_2473_, v___y_2471_, v_binders_2481_, v_entries_x3f_2477_, v___y_2478_, v___y_2479_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_a_2486_ = lean_ctor_get(v___x_2484_, 1);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2484_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2485_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
else
{
lean_object* v_a_2494_; lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
v_a_2494_ = lean_ctor_get(v___x_2484_, 0);
v_a_2495_ = lean_ctor_get(v___x_2484_, 1);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2484_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_inc(v_a_2494_);
lean_dec(v___x_2484_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2494_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
v___jp_2503_:
{
lean_object* v___x_2513_; 
v___x_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___y_2505_);
v___y_2471_ = v___y_2506_;
v___y_2472_ = v___y_2507_;
v___y_2473_ = v___y_2509_;
v___y_2474_ = v___y_2508_;
v___y_2475_ = v___y_2510_;
v___y_2476_ = v___y_2512_;
v_entries_x3f_2477_ = v___x_2513_;
v___y_2478_ = v___y_2511_;
v___y_2479_ = v___y_2504_;
goto v___jp_2470_;
}
v___jp_2515_:
{
lean_object* v___x_2521_; lean_object* v_elabName_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2521_ = lean_unsigned_to_nat(3u);
v_elabName_2522_ = l_Lean_Syntax_getArg(v_x_2463_, v___x_2521_);
v___x_2523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_elabName_2522_);
v___x_2524_ = l_Lean_Syntax_isOfKind(v_elabName_2522_, v___x_2523_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; 
lean_dec(v_elabName_2522_);
lean_dec(v_vis_x3f_2518_);
lean_dec(v___y_2517_);
lean_dec(v_x_2463_);
v___x_2525_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2520_);
return v___x_2525_;
}
else
{
lean_object* v___x_2526_; lean_object* v_type_2527_; uint8_t v___x_2528_; 
v___x_2526_ = lean_unsigned_to_nat(4u);
v_type_2527_ = l_Lean_Syntax_getArg(v_x_2463_, v___x_2526_);
lean_inc(v_type_2527_);
v___x_2528_ = l_Lean_Syntax_isOfKind(v_type_2527_, v___x_2523_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; 
lean_dec(v_type_2527_);
lean_dec(v_elabName_2522_);
lean_dec(v_vis_x3f_2518_);
lean_dec(v___y_2517_);
lean_dec(v_x_2463_);
v___x_2529_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2520_);
return v___x_2529_;
}
else
{
lean_object* v___x_2530_; lean_object* v_tk_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2530_ = lean_unsigned_to_nat(2u);
v_tk_2531_ = l_Lean_Syntax_getArg(v_x_2463_, v___x_2530_);
v___x_2532_ = lean_unsigned_to_nat(5u);
v___x_2533_ = l_Lean_Syntax_getArg(v_x_2463_, v___x_2532_);
v___x_2534_ = lean_unsigned_to_nat(6u);
v___x_2535_ = l_Lean_Syntax_getArg(v_x_2463_, v___x_2534_);
lean_dec(v_x_2463_);
v___x_2536_ = l_Lean_Syntax_isNone(v___x_2535_);
if (v___x_2536_ == 0)
{
uint8_t v___x_2537_; 
lean_inc(v___x_2535_);
v___x_2537_ = l_Lean_Syntax_matchesNull(v___x_2535_, v___y_2516_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; 
lean_dec(v___x_2535_);
lean_dec(v___x_2533_);
lean_dec(v_tk_2531_);
lean_dec(v_type_2527_);
lean_dec(v_elabName_2522_);
lean_dec(v_vis_x3f_2518_);
lean_dec(v___y_2517_);
v___x_2538_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2520_);
return v___x_2538_;
}
else
{
lean_object* v_entries_x3f_2539_; 
v_entries_x3f_2539_ = l_Lean_Syntax_getArg(v___x_2535_, v___x_2514_);
lean_dec(v___x_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2540_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_2539_);
v___x_2541_ = l_Lean_Syntax_isOfKind(v_entries_x3f_2539_, v___x_2540_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; 
lean_dec(v_entries_x3f_2539_);
lean_dec(v___x_2533_);
lean_dec(v_tk_2531_);
lean_dec(v_type_2527_);
lean_dec(v_elabName_2522_);
lean_dec(v_vis_x3f_2518_);
lean_dec(v___y_2517_);
v___x_2542_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2520_);
return v___x_2542_;
}
else
{
v___y_2504_ = v___y_2520_;
v___y_2505_ = v_entries_x3f_2539_;
v___y_2506_ = v_type_2527_;
v___y_2507_ = v_tk_2531_;
v___y_2508_ = v___y_2517_;
v___y_2509_ = v_elabName_2522_;
v___y_2510_ = v___x_2533_;
v___y_2511_ = v___y_2519_;
v___y_2512_ = v_vis_x3f_2518_;
goto v___jp_2503_;
}
}
else
{
v___y_2504_ = v___y_2520_;
v___y_2505_ = v_entries_x3f_2539_;
v___y_2506_ = v_type_2527_;
v___y_2507_ = v_tk_2531_;
v___y_2508_ = v___y_2517_;
v___y_2509_ = v_elabName_2522_;
v___y_2510_ = v___x_2533_;
v___y_2511_ = v___y_2519_;
v___y_2512_ = v_vis_x3f_2518_;
goto v___jp_2503_;
}
}
}
else
{
lean_object* v___x_2543_; 
lean_dec(v___x_2535_);
v___x_2543_ = lean_box(0);
v___y_2471_ = v_type_2527_;
v___y_2472_ = v_tk_2531_;
v___y_2473_ = v_elabName_2522_;
v___y_2474_ = v___y_2517_;
v___y_2475_ = v___x_2533_;
v___y_2476_ = v_vis_x3f_2518_;
v_entries_x3f_2477_ = v___x_2543_;
v___y_2478_ = v___y_2519_;
v___y_2479_ = v___y_2520_;
goto v___jp_2470_;
}
}
}
}
v___jp_2544_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2548_ = lean_unsigned_to_nat(1u);
v___x_2549_ = l_Lean_Syntax_getArg(v_x_2463_, v___x_2548_);
v___x_2550_ = l_Lean_Syntax_isNone(v___x_2549_);
if (v___x_2550_ == 0)
{
uint8_t v___x_2551_; 
lean_inc(v___x_2549_);
v___x_2551_ = l_Lean_Syntax_matchesNull(v___x_2549_, v___x_2548_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; 
lean_dec(v___x_2549_);
lean_dec(v_doc_x3f_2545_);
lean_dec(v_x_2463_);
v___x_2552_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2547_);
return v___x_2552_;
}
else
{
lean_object* v_vis_x3f_2553_; lean_object* v___x_2554_; 
v_vis_x3f_2553_ = l_Lean_Syntax_getArg(v___x_2549_, v___x_2514_);
lean_dec(v___x_2549_);
v___x_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2554_, 0, v_vis_x3f_2553_);
v___y_2516_ = v___x_2548_;
v___y_2517_ = v_doc_x3f_2545_;
v_vis_x3f_2518_ = v___x_2554_;
v___y_2519_ = v___y_2546_;
v___y_2520_ = v___y_2547_;
goto v___jp_2515_;
}
}
else
{
lean_object* v___x_2555_; 
lean_dec(v___x_2549_);
v___x_2555_ = lean_box(0);
v___y_2516_ = v___x_2548_;
v___y_2517_ = v_doc_x3f_2545_;
v_vis_x3f_2518_ = v___x_2555_;
v___y_2519_ = v___y_2546_;
v___y_2520_ = v___y_2547_;
goto v___jp_2515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___boxed(lean_object* v_x_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig(v_x_2568_, v_a_2569_, v_a_2570_);
lean_dec_ref(v_a_2569_);
return v_res_2571_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1(){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2579_ = l_Lean_Elab_macroAttribute;
v___x_2580_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1));
v___x_2581_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1));
v___x_2582_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___boxed), 3, 0);
v___x_2583_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2579_, v___x_2580_, v___x_2581_, v___x_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2584_;
v_res_2584_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1();
stack->m_obj
 = v_res_2584_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___boxed(lean_object* v_a_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1();
return v_res_2586_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig(lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2591_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_2592_ = lean_unsigned_to_nat(2u);
v___x_2593_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_2591_, v___x_2592_, v_a_2587_, v_a_2588_, v_a_2589_);
return v___x_2593_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2587_ = stack[0].m_obj;
lean_object* v_a_2588_ = stack[1].m_obj;
lean_object* v_a_2589_ = stack[2].m_obj;
lean_object* v_res_2594_;
v_res_2594_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig(v_a_2587_, v_a_2588_, v_a_2589_);
stack->m_obj
 = v_res_2594_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___boxed(lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig(v_a_2595_, v_a_2596_, v_a_2597_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
return v_res_2599_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0(void){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___boxed), 4, 0);
v___x_2601_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_2601_, 0, v___x_2600_);
return v___x_2601_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1(){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1));
v___x_2604_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0);
v___x_2605_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_2603_, v___x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2606_;
v_res_2606_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1();
stack->m_obj
 = v_res_2606_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___boxed(lean_object* v_a_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1();
return v_res_2608_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__0));
v___x_2611_ = l_String_toRawSubstring_x27(v___x_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1(lean_object* v___x_2613_, lean_object* v___x_2614_, lean_object* v___x_2615_, lean_object* v___x_2616_, lean_object* v___x_2617_, lean_object* v_eval_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_quotContext_2621_; lean_object* v_currMacroScope_2622_; lean_object* v_ref_2623_; uint8_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v_quotContext_2621_ = lean_ctor_get(v___y_2619_, 1);
v_currMacroScope_2622_ = lean_ctor_get(v___y_2619_, 2);
v_ref_2623_ = lean_ctor_get(v___y_2619_, 5);
v___x_2624_ = 0;
v___x_2625_ = l_Lean_SourceInfo_fromRef(v_ref_2623_, v___x_2624_);
v___x_2626_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82));
lean_inc_ref(v___x_2613_);
v___x_2627_ = l_Lean_Name_mkStr4(v___x_2613_, v___x_2614_, v___x_2615_, v___x_2626_);
v___x_2628_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1, &l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1_once, _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1);
v___x_2629_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__2));
lean_inc_ref(v___x_2616_);
v___x_2630_ = l_Lean_Name_mkStr2(v___x_2616_, v___x_2629_);
lean_inc(v_currMacroScope_2622_);
lean_inc(v_quotContext_2621_);
v___x_2631_ = l_Lean_addMacroScope(v_quotContext_2621_, v___x_2630_, v_currMacroScope_2622_);
v___x_2632_ = l_Lean_Name_mkStr4(v___x_2613_, v___x_2617_, v___x_2616_, v___x_2629_);
v___x_2633_ = lean_box(0);
lean_inc(v___x_2632_);
v___x_2634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2632_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2632_);
v___x_2636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
lean_ctor_set(v___x_2636_, 1, v___x_2633_);
v___x_2637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2634_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
lean_inc_n(v___x_2625_, 2);
v___x_2638_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2625_);
lean_ctor_set(v___x_2638_, 1, v___x_2628_);
lean_ctor_set(v___x_2638_, 2, v___x_2631_);
lean_ctor_set(v___x_2638_, 3, v___x_2637_);
v___x_2639_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5));
v___x_2640_ = l_Lean_Syntax_node1(v___x_2625_, v___x_2639_, v_eval_2618_);
v___x_2641_ = l_Lean_Syntax_node2(v___x_2625_, v___x_2627_, v___x_2638_, v___x_2640_);
v___x_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
lean_ctor_set(v___x_2642_, 1, v___y_2620_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___boxed(lean_object* v___x_2643_, lean_object* v___x_2644_, lean_object* v___x_2645_, lean_object* v___x_2646_, lean_object* v___x_2647_, lean_object* v_eval_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1(v___x_2643_, v___x_2644_, v___x_2645_, v___x_2646_, v___x_2647_, v_eval_2648_, v___y_2649_, v___y_2650_);
lean_dec_ref(v___y_2649_);
return v_res_2651_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4));
v___x_2671_ = l_Lean_mkCIdent(v___x_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig(lean_object* v_x_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2675_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1));
lean_inc(v_x_2672_);
v___x_2676_ = l_Lean_Syntax_isOfKind(v_x_2672_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; 
lean_dec(v_x_2672_);
v___x_2677_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2674_);
return v___x_2677_;
}
else
{
lean_object* v___f_2678_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v_entries_x3f_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___x_2723_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v_vis_x3f_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v_doc_x3f_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___f_2678_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2));
v___x_2723_ = lean_unsigned_to_nat(0u);
v___x_2765_ = l_Lean_Syntax_getArg(v_x_2672_, v___x_2723_);
v___x_2766_ = l_Lean_Syntax_isNone(v___x_2765_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2767_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2765_);
v___x_2768_ = l_Lean_Syntax_matchesNull(v___x_2765_, v___x_2767_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; 
lean_dec(v___x_2765_);
lean_dec(v_x_2672_);
v___x_2769_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2674_);
return v___x_2769_;
}
else
{
lean_object* v_doc_x3f_2770_; 
v_doc_x3f_2770_ = l_Lean_Syntax_getArg(v___x_2765_, v___x_2723_);
lean_dec(v___x_2765_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2773_; uint8_t v___x_2774_; 
v___x_2773_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_2770_);
v___x_2774_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2770_, v___x_2773_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; 
lean_dec(v_doc_x3f_2770_);
lean_dec(v_x_2672_);
v___x_2775_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2674_);
return v___x_2775_;
}
else
{
goto v___jp_2771_;
}
}
else
{
goto v___jp_2771_;
}
v___jp_2771_:
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_doc_x3f_2770_);
v_doc_x3f_2754_ = v___x_2772_;
v___y_2755_ = v_a_2673_;
v___y_2756_ = v_a_2674_;
goto v___jp_2753_;
}
}
}
else
{
lean_object* v___x_2776_; 
lean_dec(v___x_2765_);
v___x_2776_ = lean_box(0);
v_doc_x3f_2754_ = v___x_2776_;
v___y_2755_ = v_a_2673_;
v___y_2756_ = v_a_2674_;
goto v___jp_2753_;
}
v___jp_2679_:
{
lean_object* v_binders_2689_; lean_object* v___f_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v_binders_2689_ = l_Lean_Syntax_getArgs(v___y_2683_);
lean_dec(v___y_2683_);
v___f_2690_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2));
v___x_2691_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5, &l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5_once, _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5);
v___x_2692_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8);
v___x_2693_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_2691_, v___f_2690_, v___x_2692_, v___f_2678_, v___y_2684_, v___y_2682_, v___y_2685_, v___y_2681_, v___y_2680_, v_binders_2689_, v_entries_x3f_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_a_2695_ = lean_ctor_get(v___x_2693_, 1);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2693_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2694_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
v_a_2703_ = lean_ctor_get(v___x_2693_, 0);
v_a_2704_ = lean_ctor_get(v___x_2693_, 1);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2693_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_inc(v_a_2703_);
lean_dec(v___x_2693_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2703_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
v___jp_2712_:
{
lean_object* v___x_2722_; 
v___x_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___y_2720_);
v___y_2680_ = v___y_2713_;
v___y_2681_ = v___y_2716_;
v___y_2682_ = v___y_2715_;
v___y_2683_ = v___y_2717_;
v___y_2684_ = v___y_2718_;
v___y_2685_ = v___y_2719_;
v_entries_x3f_2686_ = v___x_2722_;
v___y_2687_ = v___y_2714_;
v___y_2688_ = v___y_2721_;
goto v___jp_2679_;
}
v___jp_2724_:
{
lean_object* v___x_2730_; lean_object* v_elabName_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2730_ = lean_unsigned_to_nat(3u);
v_elabName_2731_ = l_Lean_Syntax_getArg(v_x_2672_, v___x_2730_);
v___x_2732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_elabName_2731_);
v___x_2733_ = l_Lean_Syntax_isOfKind(v_elabName_2731_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; 
lean_dec(v_elabName_2731_);
lean_dec(v_vis_x3f_2727_);
lean_dec(v___y_2726_);
lean_dec(v_x_2672_);
v___x_2734_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2729_);
return v___x_2734_;
}
else
{
lean_object* v___x_2735_; lean_object* v_type_2736_; uint8_t v___x_2737_; 
v___x_2735_ = lean_unsigned_to_nat(4u);
v_type_2736_ = l_Lean_Syntax_getArg(v_x_2672_, v___x_2735_);
lean_inc(v_type_2736_);
v___x_2737_ = l_Lean_Syntax_isOfKind(v_type_2736_, v___x_2732_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; 
lean_dec(v_type_2736_);
lean_dec(v_elabName_2731_);
lean_dec(v_vis_x3f_2727_);
lean_dec(v___y_2726_);
lean_dec(v_x_2672_);
v___x_2738_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2729_);
return v___x_2738_;
}
else
{
lean_object* v___x_2739_; lean_object* v_tk_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
v___x_2739_ = lean_unsigned_to_nat(2u);
v_tk_2740_ = l_Lean_Syntax_getArg(v_x_2672_, v___x_2739_);
v___x_2741_ = lean_unsigned_to_nat(5u);
v___x_2742_ = l_Lean_Syntax_getArg(v_x_2672_, v___x_2741_);
v___x_2743_ = lean_unsigned_to_nat(6u);
v___x_2744_ = l_Lean_Syntax_getArg(v_x_2672_, v___x_2743_);
lean_dec(v_x_2672_);
v___x_2745_ = l_Lean_Syntax_isNone(v___x_2744_);
if (v___x_2745_ == 0)
{
uint8_t v___x_2746_; 
lean_inc(v___x_2744_);
v___x_2746_ = l_Lean_Syntax_matchesNull(v___x_2744_, v___y_2725_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; 
lean_dec(v___x_2744_);
lean_dec(v___x_2742_);
lean_dec(v_tk_2740_);
lean_dec(v_type_2736_);
lean_dec(v_elabName_2731_);
lean_dec(v_vis_x3f_2727_);
lean_dec(v___y_2726_);
v___x_2747_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2729_);
return v___x_2747_;
}
else
{
lean_object* v_entries_x3f_2748_; 
v_entries_x3f_2748_ = l_Lean_Syntax_getArg(v___x_2744_, v___x_2723_);
lean_dec(v___x_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___x_2749_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_2748_);
v___x_2750_ = l_Lean_Syntax_isOfKind(v_entries_x3f_2748_, v___x_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; 
lean_dec(v_entries_x3f_2748_);
lean_dec(v___x_2742_);
lean_dec(v_tk_2740_);
lean_dec(v_type_2736_);
lean_dec(v_elabName_2731_);
lean_dec(v_vis_x3f_2727_);
lean_dec(v___y_2726_);
v___x_2751_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2729_);
return v___x_2751_;
}
else
{
v___y_2713_ = v_type_2736_;
v___y_2714_ = v___y_2728_;
v___y_2715_ = v_vis_x3f_2727_;
v___y_2716_ = v_elabName_2731_;
v___y_2717_ = v___x_2742_;
v___y_2718_ = v___y_2726_;
v___y_2719_ = v_tk_2740_;
v___y_2720_ = v_entries_x3f_2748_;
v___y_2721_ = v___y_2729_;
goto v___jp_2712_;
}
}
else
{
v___y_2713_ = v_type_2736_;
v___y_2714_ = v___y_2728_;
v___y_2715_ = v_vis_x3f_2727_;
v___y_2716_ = v_elabName_2731_;
v___y_2717_ = v___x_2742_;
v___y_2718_ = v___y_2726_;
v___y_2719_ = v_tk_2740_;
v___y_2720_ = v_entries_x3f_2748_;
v___y_2721_ = v___y_2729_;
goto v___jp_2712_;
}
}
}
else
{
lean_object* v___x_2752_; 
lean_dec(v___x_2744_);
v___x_2752_ = lean_box(0);
v___y_2680_ = v_type_2736_;
v___y_2681_ = v_elabName_2731_;
v___y_2682_ = v_vis_x3f_2727_;
v___y_2683_ = v___x_2742_;
v___y_2684_ = v___y_2726_;
v___y_2685_ = v_tk_2740_;
v_entries_x3f_2686_ = v___x_2752_;
v___y_2687_ = v___y_2728_;
v___y_2688_ = v___y_2729_;
goto v___jp_2679_;
}
}
}
}
v___jp_2753_:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v___x_2757_ = lean_unsigned_to_nat(1u);
v___x_2758_ = l_Lean_Syntax_getArg(v_x_2672_, v___x_2757_);
v___x_2759_ = l_Lean_Syntax_isNone(v___x_2758_);
if (v___x_2759_ == 0)
{
uint8_t v___x_2760_; 
lean_inc(v___x_2758_);
v___x_2760_ = l_Lean_Syntax_matchesNull(v___x_2758_, v___x_2757_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; 
lean_dec(v___x_2758_);
lean_dec(v_doc_x3f_2754_);
lean_dec(v_x_2672_);
v___x_2761_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2756_);
return v___x_2761_;
}
else
{
lean_object* v_vis_x3f_2762_; lean_object* v___x_2763_; 
v_vis_x3f_2762_ = l_Lean_Syntax_getArg(v___x_2758_, v___x_2723_);
lean_dec(v___x_2758_);
v___x_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2763_, 0, v_vis_x3f_2762_);
v___y_2725_ = v___x_2757_;
v___y_2726_ = v_doc_x3f_2754_;
v_vis_x3f_2727_ = v___x_2763_;
v___y_2728_ = v___y_2755_;
v___y_2729_ = v___y_2756_;
goto v___jp_2724_;
}
}
else
{
lean_object* v___x_2764_; 
lean_dec(v___x_2758_);
v___x_2764_ = lean_box(0);
v___y_2725_ = v___x_2757_;
v___y_2726_ = v_doc_x3f_2754_;
v_vis_x3f_2727_ = v___x_2764_;
v___y_2728_ = v___y_2755_;
v___y_2729_ = v___y_2756_;
goto v___jp_2724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___boxed(lean_object* v_x_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig(v_x_2777_, v_a_2778_, v_a_2779_);
lean_dec_ref(v_a_2778_);
return v_res_2780_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1(){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2788_ = l_Lean_Elab_macroAttribute;
v___x_2789_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1));
v___x_2790_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1));
v___x_2791_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___boxed), 3, 0);
v___x_2792_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2788_, v___x_2789_, v___x_2790_, v___x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2793_;
v_res_2793_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1();
stack->m_obj
 = v_res_2793_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___boxed(lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1();
return v_res_2795_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab(lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2800_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_2801_ = lean_unsigned_to_nat(2u);
v___x_2802_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_2800_, v___x_2801_, v_a_2796_, v_a_2797_, v_a_2798_);
return v___x_2802_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2796_ = stack[0].m_obj;
lean_object* v_a_2797_ = stack[1].m_obj;
lean_object* v_a_2798_ = stack[2].m_obj;
lean_object* v_res_2803_;
v_res_2803_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab(v_a_2796_, v_a_2797_, v_a_2798_);
stack->m_obj
 = v_res_2803_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___boxed(lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab(v_a_2804_, v_a_2805_, v_a_2806_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
return v_res_2808_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___boxed), 4, 0);
v___x_2810_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_2810_, 0, v___x_2809_);
return v___x_2810_;
}
}
lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1(){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2812_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1));
v___x_2813_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0);
v___x_2814_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_2812_, v___x_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2815_;
v_res_2815_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1();
stack->m_obj
 = v_res_2815_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___boxed(lean_object* v_a_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1();
return v_res_2817_;
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
