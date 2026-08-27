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
lean_object* l_Array_mkArray0(lean_object*);
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
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_87_ = lean_unsigned_to_nat(3u);
v___x_88_ = l_Lean_Syntax_getArg(v_x_74_, v___x_87_);
v___x_89_ = lean_box(0);
lean_inc(v___x_88_);
v___x_90_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_90_, 0, v___x_88_);
lean_closure_set(v___x_90_, 1, v___x_89_);
v___x_91_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed), 9, 2);
lean_closure_set(v___x_91_, 0, lean_box(0));
lean_closure_set(v___x_91_, 1, v___x_90_);
v___x_92_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_91_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_94_; lean_object* v_tk_95_; lean_object* v___x_96_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_a_93_);
lean_dec_ref_known(v___x_92_, 1);
v___x_94_ = lean_unsigned_to_nat(2u);
v_tk_95_ = l_Lean_Syntax_getArg(v_x_74_, v___x_94_);
lean_dec(v_x_74_);
v___x_96_ = l_Lean_Elab_ConfigEval_ensureEvalTerm(v_vis_x3f_79_, v_kind_83_, v_tk_95_, v___x_88_, v_a_93_, v___y_80_, v___y_81_);
return v___x_96_;
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
lean_dec(v___x_88_);
lean_dec(v_kind_83_);
lean_dec(v_vis_x3f_79_);
lean_dec(v_x_74_);
v_a_97_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_92_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_92_);
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
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_155_ = lean_unsigned_to_nat(3u);
v___x_156_ = l_Lean_Syntax_getArg(v_x_142_, v___x_155_);
v___x_157_ = lean_box(0);
lean_inc(v___x_156_);
v___x_158_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_158_, 0, v___x_156_);
lean_closure_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed), 9, 2);
lean_closure_set(v___x_159_, 0, lean_box(0));
lean_closure_set(v___x_159_, 1, v___x_158_);
v___x_160_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_159_, v___y_148_, v___y_149_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_162_; lean_object* v_tk_163_; lean_object* v___x_164_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_160_, 1);
v___x_162_ = lean_unsigned_to_nat(2u);
v_tk_163_ = l_Lean_Syntax_getArg(v_x_142_, v___x_162_);
lean_dec(v_x_142_);
v___x_164_ = l_Lean_Elab_ConfigEval_ensureEvalExpr(v_vis_x3f_147_, v_kind_151_, v_tk_163_, v___x_156_, v_a_161_, v___y_148_, v___y_149_);
return v___x_164_;
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec(v___x_156_);
lean_dec(v_kind_151_);
lean_dec(v_vis_x3f_147_);
lean_dec(v_x_142_);
v_a_165_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_160_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_160_);
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
v___x_215_ = l_Array_mkArray0(lean_box(0));
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
lean_inc_ref(v___y_227_);
v___x_233_ = l_Array_append___redArg(v___y_227_, v___y_232_);
lean_dec_ref(v___y_232_);
lean_inc_n(v___y_230_, 2);
lean_inc_n(v___y_224_, 3);
v___x_234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_234_, 0, v___y_224_);
lean_ctor_set(v___x_234_, 1, v___y_230_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
v___x_235_ = l_Lean_SourceInfo_fromRef(v___y_229_, v___x_222_);
lean_dec(v___y_229_);
v___x_236_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__2));
lean_inc(v___x_235_);
v___x_237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
lean_inc(v___y_225_);
lean_inc(v___y_226_);
lean_inc_ref(v___x_234_);
lean_inc(v___y_231_);
v___x_238_ = l_Lean_Syntax_node4(v___y_224_, v___y_231_, v___x_234_, v___y_226_, v___x_237_, v___y_225_);
v___x_239_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalExprInstance___closed__1));
v___x_240_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__3));
v___x_241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_235_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = l_Lean_Syntax_node4(v___y_224_, v___x_239_, v___x_234_, v___y_226_, v___x_241_, v___y_225_);
v___x_243_ = l_Lean_Syntax_node2(v___y_224_, v___y_230_, v___x_238_, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___y_228_);
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
v___y_224_ = v___x_260_;
v___y_225_ = v___x_258_;
v___y_226_ = v___x_250_;
v___y_227_ = v___x_263_;
v___y_228_ = v___y_248_;
v___y_229_ = v_tk_256_;
v___y_230_ = v___x_261_;
v___y_231_ = v___x_262_;
v___y_232_ = v___x_265_;
goto v___jp_223_;
}
else
{
lean_object* v___x_266_; 
lean_dec(v_vis_x3f_246_);
v___x_266_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___y_224_ = v___x_260_;
v___y_225_ = v___x_258_;
v___y_226_ = v___x_250_;
v___y_227_ = v___x_263_;
v___y_228_ = v___y_248_;
v___y_229_ = v_tk_256_;
v___y_230_ = v___x_261_;
v___y_231_ = v___x_262_;
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
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_314_ = lean_unsigned_to_nat(3u);
v___x_315_ = l_Lean_Syntax_getArg(v_x_301_, v___x_314_);
v___x_316_ = lean_box(0);
lean_inc(v___x_315_);
v___x_317_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_317_, 0, v___x_315_);
lean_closure_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__1___boxed), 9, 2);
lean_closure_set(v___x_318_, 0, lean_box(0));
lean_closure_set(v___x_318_, 1, v___x_317_);
v___x_319_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_318_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v___x_321_; lean_object* v_tk_322_; lean_object* v___x_323_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_319_, 1);
v___x_321_ = lean_unsigned_to_nat(2u);
v_tk_322_ = l_Lean_Syntax_getArg(v_x_301_, v___x_321_);
lean_dec(v_x_301_);
v___x_323_ = l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval(v_vis_x3f_306_, v_kind_310_, v_tk_322_, v___x_315_, v_a_320_, v___y_307_, v___y_308_);
return v___x_323_;
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec(v___x_315_);
lean_dec(v_kind_310_);
lean_dec(v_vis_x3f_306_);
lean_dec(v_x_301_);
v_a_324_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_319_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_319_);
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
uint8_t v___x_4678__boxed_441_; size_t v_i_boxed_442_; size_t v_stop_boxed_443_; lean_object* v_res_444_; 
v___x_4678__boxed_441_ = lean_unbox(v___x_436_);
v_i_boxed_442_ = lean_unbox_usize(v_i_438_);
lean_dec(v_i_438_);
v_stop_boxed_443_ = lean_unbox_usize(v_stop_439_);
lean_dec(v_stop_439_);
v_res_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_4678__boxed_441_, v_as_437_, v_i_boxed_442_, v_stop_boxed_443_, v_b_440_);
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
lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_663_; 
v_fst_496_ = lean_ctor_get(v_b_487_, 0);
v_snd_497_ = lean_ctor_get(v_b_487_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v_b_487_);
if (v_isSharedCheck_663_ == 0)
{
v___x_499_ = v_b_487_;
v_isShared_500_ = v_isSharedCheck_663_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_snd_497_);
lean_inc(v_fst_496_);
lean_dec(v_b_487_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_663_;
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
lean_object* v___x_555_; lean_object* v___y_557_; lean_object* v_fst_558_; uint8_t v_snd_559_; lean_object* v___y_565_; lean_object* v_____x_566_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; 
v___x_555_ = l_Lean_Syntax_getArg(v___x_540_, v___x_539_);
if (v___x_542_ == 0)
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7));
lean_inc(v___x_555_);
v___x_641_ = l_Lean_Syntax_isOfKind(v___x_555_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
lean_dec(v___x_555_);
lean_dec(v___x_540_);
v___x_642_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v___x_643_; 
lean_dec_ref_known(v___x_642_, 1);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v_fst_496_);
lean_ctor_set(v___x_643_, 1, v_snd_497_);
v_a_490_ = v___x_643_;
goto v___jp_489_;
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
v_a_644_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_642_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
goto v___jp_594_;
}
}
else
{
goto v___jp_594_;
}
v___jp_556_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_560_ = lean_box(0);
v___x_561_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_561_, 0, v___x_555_);
lean_ctor_set(v___x_561_, 1, v_fst_558_);
lean_ctor_set(v___x_561_, 2, v___y_557_);
lean_ctor_set(v___x_561_, 3, v___x_560_);
lean_ctor_set(v___x_561_, 4, v___x_560_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*5, v_snd_559_);
v___x_562_ = lean_array_push(v_snd_497_, v___x_561_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_fst_496_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v_a_490_ = v___x_563_;
goto v___jp_489_;
}
v___jp_564_:
{
lean_object* v_fst_567_; lean_object* v_snd_568_; uint8_t v___x_569_; 
v_fst_567_ = lean_ctor_get(v_____x_566_, 0);
lean_inc(v_fst_567_);
v_snd_568_ = lean_ctor_get(v_____x_566_, 1);
lean_inc(v_snd_568_);
lean_dec_ref(v_____x_566_);
v___x_569_ = lean_unbox(v_snd_568_);
lean_dec(v_snd_568_);
v___y_557_ = v___y_565_;
v_fst_558_ = v_fst_567_;
v_snd_559_ = v___x_569_;
goto v___jp_556_;
}
v___jp_570_:
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = l_Lean_Syntax_getArg(v___y_572_, v___x_539_);
lean_dec(v___y_572_);
lean_inc(v___x_575_);
v___x_576_ = l_Lean_Syntax_matchesNull(v___x_575_, v___x_538_);
if (v___x_576_ == 0)
{
uint8_t v___x_577_; 
v___x_577_ = l_Lean_Syntax_matchesNull(v___x_575_, v___y_571_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v___y_573_);
v___x_578_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
v___y_565_ = v___y_574_;
v_____x_566_ = v_a_579_;
goto v___jp_564_;
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec(v___y_574_);
lean_dec(v___x_555_);
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
v_a_580_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_578_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_578_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = l_Lean_TSyntax_getId(v___y_573_);
lean_dec(v___y_573_);
v___x_589_ = l_Lean_Name_eraseMacroScopes(v___x_588_);
lean_dec(v___x_588_);
v___x_590_ = 1;
v___y_557_ = v___y_574_;
v_fst_558_ = v___x_589_;
v_snd_559_ = v___x_590_;
goto v___jp_556_;
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
lean_dec(v___x_575_);
v___x_591_ = l_Lean_TSyntax_getId(v___y_573_);
lean_dec(v___y_573_);
v___x_592_ = l_Lean_Name_eraseMacroScopes(v___x_591_);
lean_dec(v___x_591_);
v___x_593_ = 0;
v___y_557_ = v___y_574_;
v_fst_558_ = v___x_592_;
v_snd_559_ = v___x_593_;
goto v___jp_556_;
}
}
v___jp_594_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_595_ = lean_unsigned_to_nat(3u);
v___x_596_ = l_Lean_Syntax_getArg(v___x_540_, v___x_595_);
lean_dec(v___x_540_);
v___x_597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__7));
lean_inc(v___x_555_);
v___x_598_ = l_Lean_Syntax_isOfKind(v___x_555_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___y_565_ = v___x_596_;
v_____x_566_ = v_a_600_;
goto v___jp_564_;
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec(v___x_596_);
lean_dec(v___x_555_);
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
v_a_601_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_599_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_599_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_609_ = l_Lean_Syntax_getArg(v___x_555_, v___x_538_);
v___x_610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__9));
lean_inc(v___x_609_);
v___x_611_ = l_Lean_Syntax_isOfKind(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__11));
v___x_613_ = l_Lean_Syntax_isOfKind(v___x_609_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v___y_565_ = v___x_596_;
v_____x_566_ = v_a_615_;
goto v___jp_564_;
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v___x_596_);
lean_dec(v___x_555_);
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
v_a_616_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_614_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_614_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = lean_box(0);
v___x_625_ = 1;
v___y_557_ = v___x_596_;
v_fst_558_ = v___x_624_;
v_snd_559_ = v___x_625_;
goto v___jp_556_;
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(2u);
v___x_627_ = l_Lean_Syntax_getArg(v___x_609_, v___x_538_);
if (v___x_542_ == 0)
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v___x_627_);
v___x_629_ = l_Lean_Syntax_isOfKind(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; 
lean_dec(v___x_627_);
lean_dec(v___x_609_);
v___x_630_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v___y_565_ = v___x_596_;
v_____x_566_ = v_a_631_;
goto v___jp_564_;
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v___x_596_);
lean_dec(v___x_555_);
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
v_a_632_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_630_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_630_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
v___y_571_ = v___x_626_;
v___y_572_ = v___x_609_;
v___y_573_ = v___x_627_;
v___y_574_ = v___x_596_;
goto v___jp_570_;
}
}
else
{
v___y_571_ = v___x_626_;
v___y_572_ = v___x_609_;
v___y_573_ = v___x_627_;
v___y_574_ = v___x_596_;
goto v___jp_570_;
}
}
}
}
}
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_652_ = l_Lean_Syntax_getArg(v___x_540_, v___x_539_);
lean_dec(v___x_540_);
v___x_653_ = l_Lean_Syntax_getArgs(v___x_652_);
lean_dec(v___x_652_);
v___x_654_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___x_655_ = lean_array_get_size(v___x_653_);
v___x_656_ = lean_nat_dec_lt(v___x_538_, v___x_655_);
if (v___x_656_ == 0)
{
lean_dec_ref(v___x_653_);
v___y_502_ = v___x_654_;
goto v___jp_501_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; lean_object* v_snd_662_; 
v___x_657_ = lean_box(v___x_656_);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___x_654_);
v___x_659_ = ((size_t)0ULL);
v___x_660_ = lean_usize_of_nat(v___x_655_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_542_, v___x_653_, v___x_659_, v___x_660_, v___x_658_);
lean_dec_ref(v___x_653_);
v_snd_662_ = lean_ctor_get(v___x_661_, 1);
lean_inc(v_snd_662_);
lean_dec_ref(v___x_661_);
v___y_502_ = v_snd_662_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___boxed(lean_object* v_as_664_, lean_object* v_sz_665_, lean_object* v_i_666_, lean_object* v_b_667_, lean_object* v___y_668_){
_start:
{
size_t v_sz_boxed_669_; size_t v_i_boxed_670_; lean_object* v_res_671_; 
v_sz_boxed_669_ = lean_unbox_usize(v_sz_665_);
lean_dec(v_sz_665_);
v_i_boxed_670_ = lean_unbox_usize(v_i_666_);
lean_dec(v_i_666_);
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_as_664_, v_sz_boxed_669_, v_i_boxed_670_, v_b_667_);
lean_dec_ref(v_as_664_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(size_t v_sz_672_, size_t v_i_673_, lean_object* v_bs_674_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = lean_usize_dec_lt(v_i_673_, v_sz_672_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_676_, 0, v_bs_674_);
return v___x_676_;
}
else
{
lean_object* v_v_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_v_677_ = lean_array_uget(v_bs_674_, v_i_673_);
v___x_678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__1));
lean_inc(v_v_677_);
v___x_679_ = l_Lean_Syntax_isOfKind(v_v_677_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
lean_dec(v_v_677_);
lean_dec_ref(v_bs_674_);
v___x_680_ = lean_box(0);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v_bs_x27_682_; size_t v___x_683_; size_t v___x_684_; lean_object* v___x_685_; 
v___x_681_ = lean_unsigned_to_nat(0u);
v_bs_x27_682_ = lean_array_uset(v_bs_674_, v_i_673_, v___x_681_);
v___x_683_ = ((size_t)1ULL);
v___x_684_ = lean_usize_add(v_i_673_, v___x_683_);
v___x_685_ = lean_array_uset(v_bs_x27_682_, v_i_673_, v_v_677_);
v_i_673_ = v___x_684_;
v_bs_674_ = v___x_685_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3___boxed(lean_object* v_sz_687_, lean_object* v_i_688_, lean_object* v_bs_689_){
_start:
{
size_t v_sz_boxed_690_; size_t v_i_boxed_691_; lean_object* v_res_692_; 
v_sz_boxed_690_ = lean_unbox_usize(v_sz_687_);
lean_dec(v_sz_687_);
v_i_boxed_691_ = lean_unbox_usize(v_i_688_);
lean_dec(v_i_688_);
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(v_sz_boxed_690_, v_i_boxed_691_, v_bs_689_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView(lean_object* v_entries_x3f_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_omitFields_708_; lean_object* v_handlers_709_; lean_object* v___x_712_; lean_object* v_omitFields_713_; lean_object* v___y_715_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v_omitFields_713_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__0));
if (lean_obj_tag(v_entries_x3f_703_) == 1)
{
lean_object* v_val_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v_val_743_ = lean_ctor_get(v_entries_x3f_703_, 0);
lean_inc_n(v_val_743_, 2);
lean_dec_ref_known(v_entries_x3f_703_, 1);
v___x_744_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
v___x_745_ = l_Lean_Syntax_isOfKind(v_val_743_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_val_743_);
v___x_746_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_746_);
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
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = l_Lean_Syntax_getArg(v_val_743_, v___x_755_);
lean_dec(v_val_743_);
v___x_757_ = l_Lean_Syntax_getArgs(v___x_756_);
lean_dec(v___x_756_);
v___x_758_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___x_759_ = lean_array_get_size(v___x_757_);
v___x_760_ = lean_nat_dec_lt(v___x_712_, v___x_759_);
if (v___x_760_ == 0)
{
lean_dec_ref(v___x_757_);
v___y_715_ = v___x_758_;
goto v___jp_714_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; size_t v___x_763_; size_t v___x_764_; lean_object* v___x_765_; lean_object* v_snd_766_; 
v___x_761_ = lean_box(v___x_760_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v___x_758_);
v___x_763_ = ((size_t)0ULL);
v___x_764_ = lean_usize_of_nat(v___x_759_);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__2(v___x_745_, v___x_757_, v___x_763_, v___x_764_, v___x_762_);
lean_dec_ref(v___x_757_);
v_snd_766_ = lean_ctor_get(v___x_765_, 1);
lean_inc(v_snd_766_);
lean_dec_ref(v___x_765_);
v___y_715_ = v_snd_766_;
goto v___jp_714_;
}
}
}
else
{
lean_dec(v_entries_x3f_703_);
v_omitFields_708_ = v_omitFields_713_;
v_handlers_709_ = v_omitFields_713_;
goto v___jp_707_;
}
v___jp_707_:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_omitFields_708_);
lean_ctor_set(v___x_710_, 1, v_handlers_709_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
v___jp_714_:
{
size_t v_sz_716_; size_t v___x_717_; lean_object* v___x_718_; 
v_sz_716_ = lean_array_size(v___y_715_);
v___x_717_ = ((size_t)0ULL);
v___x_718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__3(v_sz_716_, v___x_717_, v___y_715_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v___x_719_; lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
v___x_719_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v_val_728_; lean_object* v___x_729_; size_t v_sz_730_; lean_object* v___x_731_; 
v_val_728_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v___x_718_, 1);
v___x_729_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__1));
v_sz_730_ = lean_array_size(v_val_728_);
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_val_728_, v_sz_730_, v___x_717_, v___x_729_);
lean_dec(v_val_728_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v_fst_733_; lean_object* v_snd_734_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
v_fst_733_ = lean_ctor_get(v_a_732_, 0);
lean_inc(v_fst_733_);
v_snd_734_ = lean_ctor_get(v_a_732_, 1);
lean_inc(v_snd_734_);
lean_dec(v_a_732_);
v_omitFields_708_ = v_fst_733_;
v_handlers_709_ = v_snd_734_;
goto v___jp_707_;
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
v_a_735_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_731_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_731_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_mkEvalConfigItemView___boxed(lean_object* v_entries_x3f_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Elab_ConfigEval_mkEvalConfigItemView(v_entries_x3f_767_, v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4(lean_object* v_as_772_, size_t v_sz_773_, size_t v_i_774_, lean_object* v_b_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg(v_as_772_, v_sz_773_, v_i_774_, v_b_775_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___boxed(lean_object* v_as_780_, lean_object* v_sz_781_, lean_object* v_i_782_, lean_object* v_b_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
size_t v_sz_boxed_787_; size_t v_i_boxed_788_; lean_object* v_res_789_; 
v_sz_boxed_787_ = lean_unbox_usize(v_sz_781_);
lean_dec(v_sz_781_);
v_i_boxed_788_ = lean_unbox_usize(v_i_782_);
lean_dec(v_i_782_);
v_res_789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4(v_as_780_, v_sz_boxed_787_, v_i_boxed_788_, v_b_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec_ref(v_as_780_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd(lean_object* v_x_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v_entries_x3f_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1));
lean_inc(v_x_803_);
v___x_843_ = l_Lean_Syntax_isOfKind(v_x_803_, v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_dec(v_x_803_);
v___x_844_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_844_;
}
else
{
lean_object* v___x_845_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v_vis_x3f_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v_doc_x3f_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_892_ = l_Lean_Syntax_getArg(v_x_803_, v___x_845_);
v___x_893_ = l_Lean_Syntax_isNone(v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_892_);
v___x_895_ = l_Lean_Syntax_matchesNull(v___x_892_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec(v___x_892_);
lean_dec(v_x_803_);
v___x_896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_896_;
}
else
{
lean_object* v_doc_x3f_897_; 
v_doc_x3f_897_ = l_Lean_Syntax_getArg(v___x_892_, v___x_845_);
lean_dec(v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_897_);
v___x_901_ = l_Lean_Syntax_isOfKind(v_doc_x3f_897_, v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_dec(v_doc_x3f_897_);
lean_dec(v_x_803_);
v___x_902_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_902_;
}
else
{
goto v___jp_898_;
}
}
else
{
goto v___jp_898_;
}
v___jp_898_:
{
lean_object* v___x_899_; 
v___x_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_899_, 0, v_doc_x3f_897_);
v_doc_x3f_881_ = v___x_899_;
v___y_882_ = v_a_804_;
v___y_883_ = v_a_805_;
goto v___jp_880_;
}
}
}
else
{
lean_object* v___x_903_; 
lean_dec(v___x_892_);
v___x_903_ = lean_box(0);
v_doc_x3f_881_ = v___x_903_;
v___y_882_ = v_a_804_;
v___y_883_ = v_a_805_;
goto v___jp_880_;
}
v___jp_846_:
{
lean_object* v___x_852_; lean_object* v_kind_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_852_ = lean_unsigned_to_nat(2u);
v_kind_853_ = l_Lean_Syntax_getArg(v_x_803_, v___x_852_);
v___x_854_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
lean_inc(v_kind_853_);
v___x_855_ = l_Lean_Syntax_isOfKind(v_kind_853_, v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_dec(v_kind_853_);
lean_dec(v_vis_x3f_849_);
lean_dec(v___y_848_);
lean_dec(v_x_803_);
v___x_856_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_856_;
}
else
{
lean_object* v___x_857_; lean_object* v_fn_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_857_ = lean_unsigned_to_nat(4u);
v_fn_858_ = l_Lean_Syntax_getArg(v_x_803_, v___x_857_);
v___x_859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_fn_858_);
v___x_860_ = l_Lean_Syntax_isOfKind(v_fn_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
lean_dec(v_fn_858_);
lean_dec(v_kind_853_);
lean_dec(v_vis_x3f_849_);
lean_dec(v___y_848_);
lean_dec(v_x_803_);
v___x_861_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_861_;
}
else
{
lean_object* v___x_862_; lean_object* v_struct_863_; uint8_t v___x_864_; 
v___x_862_ = lean_unsigned_to_nat(7u);
v_struct_863_ = l_Lean_Syntax_getArg(v_x_803_, v___x_862_);
lean_inc(v_struct_863_);
v___x_864_ = l_Lean_Syntax_isOfKind(v_struct_863_, v___x_859_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
lean_dec(v_struct_863_);
lean_dec(v_fn_858_);
lean_dec(v_kind_853_);
lean_dec(v_vis_x3f_849_);
lean_dec(v___y_848_);
lean_dec(v_x_803_);
v___x_865_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_865_;
}
else
{
lean_object* v___x_866_; lean_object* v_tk_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_866_ = lean_unsigned_to_nat(3u);
v_tk_867_ = l_Lean_Syntax_getArg(v_x_803_, v___x_866_);
v___x_868_ = lean_unsigned_to_nat(5u);
v___x_869_ = l_Lean_Syntax_getArg(v_x_803_, v___x_868_);
v___x_870_ = lean_unsigned_to_nat(8u);
v___x_871_ = l_Lean_Syntax_getArg(v_x_803_, v___x_870_);
lean_dec(v_x_803_);
v___x_872_ = l_Lean_Syntax_isNone(v___x_871_);
if (v___x_872_ == 0)
{
uint8_t v___x_873_; 
lean_inc(v___x_871_);
v___x_873_ = l_Lean_Syntax_matchesNull(v___x_871_, v___y_847_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec(v___x_871_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_struct_863_);
lean_dec(v_fn_858_);
lean_dec(v_kind_853_);
lean_dec(v_vis_x3f_849_);
lean_dec(v___y_848_);
v___x_874_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_874_;
}
else
{
lean_object* v_entries_x3f_875_; 
v_entries_x3f_875_ = l_Lean_Syntax_getArg(v___x_871_, v___x_845_);
lean_dec(v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_876_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_875_);
v___x_877_ = l_Lean_Syntax_isOfKind(v_entries_x3f_875_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
lean_dec(v_entries_x3f_875_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_struct_863_);
lean_dec(v_fn_858_);
lean_dec(v_kind_853_);
lean_dec(v_vis_x3f_849_);
lean_dec(v___y_848_);
v___x_878_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_878_;
}
else
{
v___y_831_ = v_fn_858_;
v___y_832_ = v_kind_853_;
v___y_833_ = v___y_848_;
v___y_834_ = v___y_850_;
v___y_835_ = v_struct_863_;
v___y_836_ = v___x_869_;
v___y_837_ = v_vis_x3f_849_;
v___y_838_ = v_tk_867_;
v___y_839_ = v_entries_x3f_875_;
v___y_840_ = v___y_851_;
goto v___jp_830_;
}
}
else
{
v___y_831_ = v_fn_858_;
v___y_832_ = v_kind_853_;
v___y_833_ = v___y_848_;
v___y_834_ = v___y_850_;
v___y_835_ = v_struct_863_;
v___y_836_ = v___x_869_;
v___y_837_ = v_vis_x3f_849_;
v___y_838_ = v_tk_867_;
v___y_839_ = v_entries_x3f_875_;
v___y_840_ = v___y_851_;
goto v___jp_830_;
}
}
}
else
{
lean_object* v___x_879_; 
lean_dec(v___x_871_);
v___x_879_ = lean_box(0);
v___y_808_ = v_fn_858_;
v___y_809_ = v_kind_853_;
v___y_810_ = v___y_848_;
v___y_811_ = v_struct_863_;
v___y_812_ = v_tk_867_;
v___y_813_ = v_vis_x3f_849_;
v___y_814_ = v___x_869_;
v_entries_x3f_815_ = v___x_879_;
v___y_816_ = v___y_850_;
v___y_817_ = v___y_851_;
goto v___jp_807_;
}
}
}
}
}
v___jp_880_:
{
lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = l_Lean_Syntax_getArg(v_x_803_, v___x_884_);
v___x_886_ = l_Lean_Syntax_isNone(v___x_885_);
if (v___x_886_ == 0)
{
uint8_t v___x_887_; 
lean_inc(v___x_885_);
v___x_887_ = l_Lean_Syntax_matchesNull(v___x_885_, v___x_884_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
lean_dec(v___x_885_);
lean_dec(v_doc_x3f_881_);
lean_dec(v_x_803_);
v___x_888_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_elabEnsureEvalTermInstance_spec__0___redArg();
return v___x_888_;
}
else
{
lean_object* v_vis_x3f_889_; lean_object* v___x_890_; 
v_vis_x3f_889_ = l_Lean_Syntax_getArg(v___x_885_, v___x_845_);
lean_dec(v___x_885_);
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v_vis_x3f_889_);
v___y_847_ = v___x_884_;
v___y_848_ = v_doc_x3f_881_;
v_vis_x3f_849_ = v___x_890_;
v___y_850_ = v___y_882_;
v___y_851_ = v___y_883_;
goto v___jp_846_;
}
}
else
{
lean_object* v___x_891_; 
lean_dec(v___x_885_);
v___x_891_ = lean_box(0);
v___y_847_ = v___x_884_;
v___y_848_ = v_doc_x3f_881_;
v_vis_x3f_849_ = v___x_891_;
v___y_850_ = v___y_882_;
v___y_851_ = v___y_883_;
goto v___jp_846_;
}
}
}
v___jp_807_:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Elab_ConfigEval_mkEvalConfigItemView(v_entries_x3f_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v_binders_820_; lean_object* v___x_821_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v_binders_820_ = l_Lean_Syntax_getArgs(v___y_814_);
lean_dec(v___y_814_);
v___x_821_ = l_Lean_Elab_ConfigEval_defEvalConfigItem(v___y_810_, v___y_813_, v___y_809_, v___y_812_, v___y_811_, v___y_808_, v_binders_820_, v_a_819_, v___y_816_, v___y_817_);
return v___x_821_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v___y_814_);
lean_dec(v___y_813_);
lean_dec(v___y_812_);
lean_dec(v___y_811_);
lean_dec(v___y_810_);
lean_dec(v___y_809_);
lean_dec(v___y_808_);
v_a_822_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_818_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_818_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
v___jp_830_:
{
lean_object* v___x_841_; 
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v___y_839_);
v___y_808_ = v___y_831_;
v___y_809_ = v___y_832_;
v___y_810_ = v___y_833_;
v___y_811_ = v___y_835_;
v___y_812_ = v___y_838_;
v___y_813_ = v___y_837_;
v___y_814_ = v___y_836_;
v_entries_x3f_815_ = v___x_841_;
v___y_816_ = v___y_834_;
v___y_817_ = v___y_840_;
goto v___jp_807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___boxed(lean_object* v_x_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd(v_x_904_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1(){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_916_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_917_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1));
v___x_918_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___closed__1));
v___x_919_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___boxed), 4, 0);
v___x_920_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_916_, v___x_917_, v___x_918_, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1___boxed(lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___regBuiltin_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd__1();
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd(lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_929_ = lean_unsigned_to_nat(2u);
v___x_930_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_928_, v___x_929_, v_a_924_, v_a_925_, v_a_926_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___boxed(lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd(v_a_931_, v_a_932_, v_a_933_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
return v_res_935_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___boxed), 4, 0);
v___x_937_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1(){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1));
v___x_940_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___closed__0);
v___x_941_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_939_, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1___boxed(lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd__1();
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(size_t v_sz_944_, size_t v_i_945_, lean_object* v_bs_946_){
_start:
{
uint8_t v___x_947_; 
v___x_947_ = lean_usize_dec_lt(v_i_945_, v_sz_944_);
if (v___x_947_ == 0)
{
return v_bs_946_;
}
else
{
lean_object* v_v_948_; lean_object* v___x_949_; lean_object* v_bs_x27_950_; size_t v___x_951_; size_t v___x_952_; lean_object* v___x_953_; 
v_v_948_ = lean_array_uget(v_bs_946_, v_i_945_);
v___x_949_ = lean_unsigned_to_nat(0u);
v_bs_x27_950_ = lean_array_uset(v_bs_946_, v_i_945_, v___x_949_);
v___x_951_ = ((size_t)1ULL);
v___x_952_ = lean_usize_add(v_i_945_, v___x_951_);
v___x_953_ = lean_array_uset(v_bs_x27_950_, v_i_945_, v_v_948_);
v_i_945_ = v___x_952_;
v_bs_946_ = v___x_953_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0___boxed(lean_object* v_sz_955_, lean_object* v_i_956_, lean_object* v_bs_957_){
_start:
{
size_t v_sz_boxed_958_; size_t v_i_boxed_959_; lean_object* v_res_960_; 
v_sz_boxed_958_ = lean_unbox_usize(v_sz_955_);
lean_dec(v_sz_955_);
v_i_boxed_959_ = lean_unbox_usize(v_i_956_);
lean_dec(v_i_956_);
v_res_960_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_boxed_958_, v_i_boxed_959_, v_bs_957_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(lean_object* v_stx_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_989_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1));
lean_inc(v_stx_986_);
v___x_990_ = l_Lean_Syntax_isOfKind(v_stx_986_, v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__3));
lean_inc(v_stx_986_);
v___x_992_ = l_Lean_Syntax_isOfKind(v_stx_986_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__5));
lean_inc(v_stx_986_);
v___x_994_ = l_Lean_Syntax_isOfKind(v_stx_986_, v___x_993_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_995_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__7));
lean_inc(v_stx_986_);
v___x_996_ = l_Lean_Syntax_isOfKind(v_stx_986_, v___x_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_998_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_986_, v___x_997_, v_a_987_, v_a_988_);
lean_dec(v_stx_986_);
return v___x_998_;
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = lean_unsigned_to_nat(1u);
v___x_1001_ = l_Lean_Syntax_getArg(v_stx_986_, v___x_1000_);
v___x_1002_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1001_);
v___x_1003_ = l_Lean_Syntax_matchesNull(v___x_1001_, v___x_1002_);
if (v___x_1003_ == 0)
{
uint8_t v___x_1004_; 
v___x_1004_ = l_Lean_Syntax_matchesNull(v___x_1001_, v___x_999_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_1006_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_986_, v___x_1005_, v_a_987_, v_a_988_);
lean_dec(v_stx_986_);
return v___x_1006_;
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1007_ = l_Lean_mkHole(v_stx_986_, v___x_1003_);
lean_dec(v_stx_986_);
v___x_1008_ = lean_mk_empty_array_with_capacity(v___x_1000_);
v___x_1009_ = lean_array_push(v___x_1008_, v___x_1007_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v_a_988_);
return v___x_1010_;
}
}
else
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Syntax_getArg(v___x_1001_, v___x_999_);
lean_dec(v___x_1001_);
if (v___x_994_ == 0)
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v___x_1011_);
v___x_1017_ = l_Lean_Syntax_isOfKind(v___x_1011_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_dec(v___x_1011_);
v___x_1018_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_1019_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_986_, v___x_1018_, v_a_987_, v_a_988_);
lean_dec(v_stx_986_);
return v___x_1019_;
}
else
{
lean_dec(v_stx_986_);
goto v___jp_1012_;
}
}
else
{
lean_dec(v_stx_986_);
goto v___jp_1012_;
}
v___jp_1012_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = lean_mk_empty_array_with_capacity(v___x_1000_);
v___x_1014_ = lean_array_push(v___x_1013_, v___x_1011_);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v_a_988_);
return v___x_1015_;
}
}
}
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1020_ = lean_unsigned_to_nat(2u);
v___x_1021_ = l_Lean_Syntax_getArg(v_stx_986_, v___x_1020_);
v___x_1022_ = l_Lean_Syntax_matchesNull(v___x_1021_, v___x_1020_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_1024_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_986_, v___x_1023_, v_a_987_, v_a_988_);
lean_dec(v_stx_986_);
return v___x_1024_;
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_ids_1027_; size_t v_sz_1028_; size_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1025_ = lean_unsigned_to_nat(1u);
v___x_1026_ = l_Lean_Syntax_getArg(v_stx_986_, v___x_1025_);
lean_dec(v_stx_986_);
v_ids_1027_ = l_Lean_Syntax_getArgs(v___x_1026_);
lean_dec(v___x_1026_);
v_sz_1028_ = lean_array_size(v_ids_1027_);
v___x_1029_ = ((size_t)0ULL);
v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_1028_, v___x_1029_, v_ids_1027_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v_a_988_);
return v___x_1031_;
}
}
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___y_1035_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1032_ = lean_unsigned_to_nat(1u);
v___x_1033_ = l_Lean_Syntax_getArg(v_stx_986_, v___x_1032_);
v___x_1041_ = lean_unsigned_to_nat(2u);
v___x_1042_ = l_Lean_Syntax_getArg(v_stx_986_, v___x_1041_);
v___x_1043_ = l_Lean_Syntax_isNone(v___x_1042_);
if (v___x_1043_ == 0)
{
uint8_t v___x_1044_; 
v___x_1044_ = l_Lean_Syntax_matchesNull(v___x_1042_, v___x_1041_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec(v___x_1033_);
v___x_1045_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_1046_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_986_, v___x_1045_, v_a_987_, v_a_988_);
lean_dec(v_stx_986_);
return v___x_1046_;
}
else
{
lean_dec(v_stx_986_);
v___y_1035_ = v_a_988_;
goto v___jp_1034_;
}
}
else
{
lean_dec(v___x_1042_);
lean_dec(v_stx_986_);
v___y_1035_ = v_a_988_;
goto v___jp_1034_;
}
v___jp_1034_:
{
lean_object* v_ids_1036_; size_t v_sz_1037_; size_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_ids_1036_ = l_Lean_Syntax_getArgs(v___x_1033_);
lean_dec(v___x_1033_);
v_sz_1037_ = lean_array_size(v_ids_1036_);
v___x_1038_ = ((size_t)0ULL);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_1037_, v___x_1038_, v_ids_1036_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___y_1035_);
return v___x_1040_;
}
}
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___y_1050_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1047_ = lean_unsigned_to_nat(1u);
v___x_1048_ = l_Lean_Syntax_getArg(v_stx_986_, v___x_1047_);
v___x_1056_ = lean_unsigned_to_nat(2u);
v___x_1057_ = l_Lean_Syntax_getArg(v_stx_986_, v___x_1056_);
v___x_1058_ = l_Lean_Syntax_isNone(v___x_1057_);
if (v___x_1058_ == 0)
{
uint8_t v___x_1059_; 
v___x_1059_ = l_Lean_Syntax_matchesNull(v___x_1057_, v___x_1056_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_dec(v___x_1048_);
v___x_1060_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__8));
v___x_1061_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_986_, v___x_1060_, v_a_987_, v_a_988_);
lean_dec(v_stx_986_);
return v___x_1061_;
}
else
{
lean_dec(v_stx_986_);
v___y_1050_ = v_a_988_;
goto v___jp_1049_;
}
}
else
{
lean_dec(v___x_1057_);
lean_dec(v_stx_986_);
v___y_1050_ = v_a_988_;
goto v___jp_1049_;
}
v___jp_1049_:
{
lean_object* v_ids_1051_; size_t v_sz_1052_; size_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_ids_1051_ = l_Lean_Syntax_getArgs(v___x_1048_);
lean_dec(v___x_1048_);
v_sz_1052_ = lean_array_size(v_ids_1051_);
v___x_1053_ = ((size_t)0ULL);
v___x_1054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs_spec__0(v_sz_1052_, v___x_1053_, v_ids_1051_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v___y_1050_);
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___boxed(lean_object* v_stx_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(v_stx_1062_, v_a_1063_, v_a_1064_);
lean_dec_ref(v_a_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(lean_object* v_as_1066_, size_t v_i_1067_, size_t v_stop_1068_, lean_object* v_b_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_a_1073_; lean_object* v_a_1074_; uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_eq(v_i_1067_, v_stop_1068_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_array_uget_borrowed(v_as_1066_, v_i_1067_);
lean_inc(v___x_1079_);
v___x_1080_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs(v___x_1079_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v_a_1082_; lean_object* v___x_1083_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
v_a_1082_ = lean_ctor_get(v___x_1080_, 1);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1080_, 2);
v___x_1083_ = l_Array_append___redArg(v_b_1069_, v_a_1081_);
lean_dec(v_a_1081_);
v_a_1073_ = v___x_1083_;
v_a_1074_ = v_a_1082_;
goto v___jp_1072_;
}
else
{
lean_dec_ref(v_b_1069_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1084_; lean_object* v_a_1085_; 
v_a_1084_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1084_);
v_a_1085_ = lean_ctor_get(v___x_1080_, 1);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1080_, 2);
v_a_1073_ = v_a_1084_;
v_a_1074_ = v_a_1085_;
goto v___jp_1072_;
}
else
{
return v___x_1080_;
}
}
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_b_1069_);
lean_ctor_set(v___x_1086_, 1, v___y_1071_);
return v___x_1086_;
}
v___jp_1072_:
{
size_t v___x_1075_; size_t v___x_1076_; 
v___x_1075_ = ((size_t)1ULL);
v___x_1076_ = lean_usize_add(v_i_1067_, v___x_1075_);
v_i_1067_ = v___x_1076_;
v_b_1069_ = v_a_1073_;
v___y_1071_ = v_a_1074_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3___boxed(lean_object* v_as_1087_, lean_object* v_i_1088_, lean_object* v_stop_1089_, lean_object* v_b_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
size_t v_i_boxed_1093_; size_t v_stop_boxed_1094_; lean_object* v_res_1095_; 
v_i_boxed_1093_ = lean_unbox_usize(v_i_1088_);
lean_dec(v_i_1088_);
v_stop_boxed_1094_ = lean_unbox_usize(v_stop_1089_);
lean_dec(v_stop_1089_);
v_res_1095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_as_1087_, v_i_boxed_1093_, v_stop_boxed_1094_, v_b_1090_, v___y_1091_, v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec_ref(v_as_1087_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(size_t v_sz_1096_, size_t v_i_1097_, lean_object* v_bs_1098_){
_start:
{
uint8_t v___x_1099_; 
v___x_1099_ = lean_usize_dec_lt(v_i_1097_, v_sz_1096_);
if (v___x_1099_ == 0)
{
return v_bs_1098_;
}
else
{
lean_object* v_v_1100_; lean_object* v___x_1101_; lean_object* v_bs_x27_1102_; size_t v___x_1103_; size_t v___x_1104_; lean_object* v___x_1105_; 
v_v_1100_ = lean_array_uget(v_bs_1098_, v_i_1097_);
v___x_1101_ = lean_unsigned_to_nat(0u);
v_bs_x27_1102_ = lean_array_uset(v_bs_1098_, v_i_1097_, v___x_1101_);
v___x_1103_ = ((size_t)1ULL);
v___x_1104_ = lean_usize_add(v_i_1097_, v___x_1103_);
v___x_1105_ = lean_array_uset(v_bs_x27_1102_, v_i_1097_, v_v_1100_);
v_i_1097_ = v___x_1104_;
v_bs_1098_ = v___x_1105_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2___boxed(lean_object* v_sz_1107_, lean_object* v_i_1108_, lean_object* v_bs_1109_){
_start:
{
size_t v_sz_boxed_1110_; size_t v_i_boxed_1111_; lean_object* v_res_1112_; 
v_sz_boxed_1110_ = lean_unbox_usize(v_sz_1107_);
lean_dec(v_sz_1107_);
v_i_boxed_1111_ = lean_unbox_usize(v_i_1108_);
lean_dec(v_i_1108_);
v_res_1112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(v_sz_boxed_1110_, v_i_boxed_1111_, v_bs_1109_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(size_t v_sz_1113_, size_t v_i_1114_, lean_object* v_bs_1115_){
_start:
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_usize_dec_lt(v_i_1114_, v_sz_1113_);
if (v___x_1116_ == 0)
{
return v_bs_1115_;
}
else
{
lean_object* v_v_1117_; lean_object* v___x_1118_; lean_object* v_bs_x27_1119_; size_t v___x_1120_; size_t v___x_1121_; lean_object* v___x_1122_; 
v_v_1117_ = lean_array_uget(v_bs_1115_, v_i_1114_);
v___x_1118_ = lean_unsigned_to_nat(0u);
v_bs_x27_1119_ = lean_array_uset(v_bs_1115_, v_i_1114_, v___x_1118_);
v___x_1120_ = ((size_t)1ULL);
v___x_1121_ = lean_usize_add(v_i_1114_, v___x_1120_);
v___x_1122_ = lean_array_uset(v_bs_x27_1119_, v_i_1114_, v_v_1117_);
v_i_1114_ = v___x_1121_;
v_bs_1115_ = v___x_1122_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0___boxed(lean_object* v_sz_1124_, lean_object* v_i_1125_, lean_object* v_bs_1126_){
_start:
{
size_t v_sz_boxed_1127_; size_t v_i_boxed_1128_; lean_object* v_res_1129_; 
v_sz_boxed_1127_ = lean_unbox_usize(v_sz_1124_);
lean_dec(v_sz_1124_);
v_i_boxed_1128_ = lean_unbox_usize(v_i_1125_);
lean_dec(v_i_1125_);
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_boxed_1127_, v_i_boxed_1128_, v_bs_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(size_t v_sz_1130_, size_t v_i_1131_, lean_object* v_bs_1132_){
_start:
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_usize_dec_lt(v_i_1131_, v_sz_1130_);
if (v___x_1133_ == 0)
{
return v_bs_1132_;
}
else
{
lean_object* v_v_1134_; lean_object* v___x_1135_; lean_object* v_bs_x27_1136_; size_t v___x_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
v_v_1134_ = lean_array_uget(v_bs_1132_, v_i_1131_);
v___x_1135_ = lean_unsigned_to_nat(0u);
v_bs_x27_1136_ = lean_array_uset(v_bs_1132_, v_i_1131_, v___x_1135_);
v___x_1137_ = ((size_t)1ULL);
v___x_1138_ = lean_usize_add(v_i_1131_, v___x_1137_);
v___x_1139_ = lean_array_uset(v_bs_x27_1136_, v_i_1131_, v_v_1134_);
v_i_1131_ = v___x_1138_;
v_bs_1132_ = v___x_1139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1___boxed(lean_object* v_sz_1141_, lean_object* v_i_1142_, lean_object* v_bs_1143_){
_start:
{
size_t v_sz_boxed_1144_; size_t v_i_boxed_1145_; lean_object* v_res_1146_; 
v_sz_boxed_1144_ = lean_unbox_usize(v_sz_1141_);
lean_dec(v_sz_1141_);
v_i_boxed_1145_ = lean_unbox_usize(v_i_1142_);
lean_dec(v_i_1142_);
v_res_1146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(v_sz_boxed_1144_, v_i_boxed_1145_, v_bs_1143_);
return v_res_1146_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__6));
v___x_1156_ = l_String_toRawSubstring_x27(v___x_1155_);
return v___x_1156_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__25));
v___x_1197_ = l_String_toRawSubstring_x27(v___x_1196_);
return v___x_1197_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__53));
v___x_1270_ = l_String_toRawSubstring_x27(v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__56));
v___x_1274_ = l_String_toRawSubstring_x27(v___x_1273_);
return v___x_1274_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__59));
v___x_1279_ = l_String_toRawSubstring_x27(v___x_1278_);
return v___x_1279_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74));
v___x_1311_ = l_Lean_mkIdent(v___x_1310_);
return v___x_1311_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__77));
v___x_1316_ = l_Lean_mkIdent(v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__80));
v___x_1321_ = l_Lean_mkIdent(v___x_1320_);
return v___x_1321_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__84));
v___x_1330_ = l_String_toRawSubstring_x27(v___x_1329_);
return v___x_1330_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__92));
v___x_1350_ = l_String_toRawSubstring_x27(v___x_1349_);
return v___x_1350_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__98));
v___x_1362_ = l_String_toRawSubstring_x27(v___x_1361_);
return v___x_1362_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__73));
v___x_1368_ = l_String_toRawSubstring_x27(v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(lean_object* v_monad_1386_, lean_object* v_mkMonadAdapt_1387_, lean_object* v_logExceptionsDefault_1388_, lean_object* v_mkLogExceptionsTerm_1389_, lean_object* v_doc_x3f_1390_, lean_object* v_vis_x3f_1391_, lean_object* v_tk_1392_, lean_object* v_elabName_1393_, lean_object* v_type_1394_, lean_object* v_binders_1395_, lean_object* v_entries_x3f_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; size_t v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; size_t v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; size_t v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; size_t v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; size_t v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; size_t v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v_a_1712_; lean_object* v_a_1713_; lean_object* v___y_1816_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__0));
v___x_1401_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__0));
v___x_1402_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__1));
v___x_1828_ = lean_array_get_size(v_binders_1395_);
v___x_1829_ = lean_nat_dec_lt(v___x_1399_, v___x_1828_);
if (v___x_1829_ == 0)
{
v_a_1712_ = v___x_1400_;
v_a_1713_ = v_a_1398_;
goto v___jp_1711_;
}
else
{
uint8_t v___x_1830_; 
v___x_1830_ = lean_nat_dec_le(v___x_1828_, v___x_1828_);
if (v___x_1830_ == 0)
{
if (v___x_1829_ == 0)
{
v_a_1712_ = v___x_1400_;
v_a_1713_ = v_a_1398_;
goto v___jp_1711_;
}
else
{
size_t v___x_1831_; size_t v___x_1832_; lean_object* v___x_1833_; 
v___x_1831_ = ((size_t)0ULL);
v___x_1832_ = lean_usize_of_nat(v___x_1828_);
v___x_1833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_binders_1395_, v___x_1831_, v___x_1832_, v___x_1400_, v_a_1397_, v_a_1398_);
v___y_1816_ = v___x_1833_;
goto v___jp_1815_;
}
}
else
{
size_t v___x_1834_; size_t v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = ((size_t)0ULL);
v___x_1835_ = lean_usize_of_nat(v___x_1828_);
v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__3(v_binders_1395_, v___x_1834_, v___x_1835_, v___x_1400_, v_a_1397_, v_a_1398_);
v___y_1816_ = v___x_1836_;
goto v___jp_1815_;
}
}
v___jp_1403_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; size_t v_sz_1458_; lean_object* v___x_1459_; size_t v_sz_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_inc_ref_n(v___y_1435_, 2);
v___x_1440_ = l_Array_append___redArg(v___y_1435_, v___y_1439_);
lean_dec_ref(v___y_1439_);
lean_inc_n(v___y_1418_, 18);
lean_inc_n(v___y_1412_, 77);
v___x_1441_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1441_, 0, v___y_1412_);
lean_ctor_set(v___x_1441_, 1, v___y_1418_);
lean_ctor_set(v___x_1441_, 2, v___x_1440_);
lean_inc_n(v___y_1433_, 22);
v___x_1442_ = l_Lean_Syntax_node7(v___y_1412_, v___y_1428_, v___y_1413_, v___y_1433_, v___x_1441_, v___y_1433_, v___y_1433_, v___y_1433_, v___y_1433_);
v___x_1443_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__1));
lean_inc_ref_n(v___y_1408_, 4);
v___x_1444_ = l_Lean_Name_mkStr4(v___x_1401_, v___x_1402_, v___y_1408_, v___x_1443_);
v___x_1445_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__2));
v___x_1446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___y_1412_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__3));
v___x_1448_ = l_Lean_Name_mkStr4(v___x_1401_, v___x_1402_, v___y_1408_, v___x_1447_);
lean_inc_n(v___y_1405_, 2);
v___x_1449_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1405_);
lean_ctor_set(v___x_1449_, 1, v___y_1418_);
lean_ctor_set(v___x_1449_, 2, v___x_1400_);
v___x_1450_ = lean_unsigned_to_nat(2u);
v___x_1451_ = lean_mk_empty_array_with_capacity(v___x_1450_);
v___x_1452_ = lean_array_push(v___x_1451_, v_elabName_1393_);
v___x_1453_ = lean_array_push(v___x_1452_, v___x_1449_);
v___x_1454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1454_, 0, v___y_1405_);
lean_ctor_set(v___x_1454_, 1, v___x_1448_);
lean_ctor_set(v___x_1454_, 2, v___x_1453_);
v___x_1455_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__4));
v___x_1456_ = l_Lean_Name_mkStr4(v___x_1401_, v___x_1402_, v___y_1408_, v___x_1455_);
v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__1(v___y_1420_, v___y_1415_, v_binders_1395_);
v_sz_1458_ = lean_array_size(v___x_1457_);
v___x_1459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__2(v_sz_1458_, v___y_1415_, v___x_1457_);
v_sz_1460_ = lean_array_size(v___x_1459_);
v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_1460_, v___y_1415_, v___x_1459_);
v___x_1462_ = l_Array_append___redArg(v___y_1435_, v___x_1461_);
lean_dec_ref(v___x_1461_);
v___x_1463_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_getBracketedBinderArgs___closed__1));
lean_inc_ref(v___y_1437_);
v___x_1464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___y_1412_);
lean_ctor_set(v___x_1464_, 1, v___y_1437_);
v___x_1465_ = l_Lean_Syntax_node1(v___y_1412_, v___y_1418_, v___y_1416_);
v___x_1466_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__5));
v___x_1467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___y_1412_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__7);
v___x_1469_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__9));
lean_inc_n(v___y_1438_, 5);
lean_inc_n(v___y_1427_, 5);
v___x_1470_ = l_Lean_addMacroScope(v___y_1427_, v___x_1469_, v___y_1438_);
lean_inc_n(v___y_1436_, 5);
v___x_1471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___y_1436_);
v___x_1472_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__10));
lean_inc_n(v___y_1429_, 8);
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___y_1429_);
v___x_1474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1471_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1475_, 0, v___y_1412_);
lean_ctor_set(v___x_1475_, 1, v___x_1468_);
lean_ctor_set(v___x_1475_, 2, v___x_1470_);
lean_ctor_set(v___x_1475_, 3, v___x_1474_);
lean_inc_ref_n(v___x_1467_, 4);
v___x_1476_ = l_Lean_Syntax_node2(v___y_1412_, v___y_1418_, v___x_1467_, v___x_1475_);
lean_inc_ref(v___y_1404_);
v___x_1477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___y_1412_);
lean_ctor_set(v___x_1477_, 1, v___y_1404_);
lean_inc_ref_n(v___x_1477_, 3);
lean_inc_ref_n(v___x_1464_, 3);
v___x_1478_ = l_Lean_Syntax_node5(v___y_1412_, v___x_1463_, v___x_1464_, v___x_1465_, v___x_1476_, v___y_1433_, v___x_1477_);
v___x_1479_ = lean_array_push(v___x_1462_, v___x_1478_);
v___x_1480_ = l_Lean_Syntax_node1(v___y_1412_, v___y_1418_, v___y_1422_);
lean_inc_n(v_type_1394_, 2);
v___x_1481_ = l_Lean_Syntax_node2(v___y_1412_, v___y_1418_, v___x_1467_, v_type_1394_);
v___x_1482_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__12));
lean_inc_ref(v___y_1411_);
v___x_1483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___y_1412_);
lean_ctor_set(v___x_1483_, 1, v___y_1411_);
v___x_1484_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__14));
v___x_1485_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__16));
v___x_1486_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__17));
v___x_1487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___y_1412_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__18));
v___x_1489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___y_1412_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
lean_inc_ref(v___x_1489_);
lean_inc_ref(v___x_1487_);
v___x_1490_ = l_Lean_Syntax_node2(v___y_1412_, v___x_1485_, v___x_1487_, v___x_1489_);
v___x_1491_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__20));
v___x_1492_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__22));
v___x_1493_ = l_Lean_Syntax_node1(v___y_1412_, v___x_1492_, v___y_1433_);
v___x_1494_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__24));
v___x_1495_ = l_Lean_Syntax_node1(v___y_1412_, v___x_1494_, v___y_1433_);
v___x_1496_ = l_Lean_Syntax_node6(v___y_1412_, v___x_1491_, v___x_1487_, v___y_1433_, v___x_1493_, v___x_1495_, v___y_1433_, v___x_1489_);
v___x_1497_ = l_Lean_Syntax_node2(v___y_1412_, v___x_1484_, v___x_1490_, v___x_1496_);
lean_inc_ref_n(v___x_1483_, 5);
v___x_1498_ = l_Lean_Syntax_node2(v___y_1412_, v___x_1482_, v___x_1483_, v___x_1497_);
v___x_1499_ = l_Lean_Syntax_node1(v___y_1412_, v___y_1418_, v___x_1498_);
v___x_1500_ = l_Lean_Syntax_node5(v___y_1412_, v___x_1463_, v___x_1464_, v___x_1480_, v___x_1481_, v___x_1499_, v___x_1477_);
v___x_1501_ = lean_array_push(v___x_1479_, v___x_1500_);
v___x_1502_ = l_Lean_Syntax_node1(v___y_1412_, v___y_1418_, v___y_1406_);
v___x_1503_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__26);
v___x_1504_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__27));
v___x_1505_ = l_Lean_addMacroScope(v___y_1427_, v___x_1504_, v___y_1438_);
v___x_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___y_1436_);
v___x_1507_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__29));
v___x_1508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set(v___x_1508_, 1, v___y_1429_);
v___x_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1506_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1510_, 0, v___y_1412_);
lean_ctor_set(v___x_1510_, 1, v___x_1503_);
lean_ctor_set(v___x_1510_, 2, v___x_1505_);
lean_ctor_set(v___x_1510_, 3, v___x_1509_);
v___x_1511_ = l_Lean_Syntax_node2(v___y_1412_, v___y_1418_, v___x_1467_, v___x_1510_);
v___x_1512_ = l_Lean_Syntax_node2(v___y_1412_, v___x_1482_, v___x_1483_, v_logExceptionsDefault_1388_);
v___x_1513_ = l_Lean_Syntax_node1(v___y_1412_, v___y_1418_, v___x_1512_);
v___x_1514_ = l_Lean_Syntax_node5(v___y_1412_, v___x_1463_, v___x_1464_, v___x_1502_, v___x_1511_, v___x_1513_, v___x_1477_);
v___x_1515_ = lean_array_push(v___x_1501_, v___x_1514_);
v___x_1516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1516_, 0, v___y_1412_);
lean_ctor_set(v___x_1516_, 1, v___y_1418_);
lean_ctor_set(v___x_1516_, 2, v___x_1515_);
v___x_1517_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__31));
v___x_1518_ = l_Lean_Syntax_node1(v___y_1412_, v___y_1418_, v_type_1394_);
lean_inc(v___x_1518_);
lean_inc_n(v___y_1432_, 4);
v___x_1519_ = l_Lean_Syntax_node2(v___y_1412_, v___y_1432_, v_monad_1386_, v___x_1518_);
v___x_1520_ = l_Lean_Syntax_node2(v___y_1412_, v___x_1517_, v___x_1467_, v___x_1519_);
v___x_1521_ = l_Lean_Syntax_node1(v___y_1412_, v___y_1418_, v___x_1520_);
v___x_1522_ = l_Lean_Syntax_node2(v___y_1412_, v___x_1456_, v___x_1516_, v___x_1521_);
v___x_1523_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__32));
v___x_1524_ = l_Lean_Name_mkStr4(v___x_1401_, v___x_1402_, v___y_1408_, v___x_1523_);
v___x_1525_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__33));
v___x_1526_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__34));
v___x_1527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___y_1412_);
lean_ctor_set(v___x_1527_, 1, v___x_1525_);
v___x_1528_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__36));
v___x_1529_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__38));
v___x_1530_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__40));
v___x_1531_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__41));
v___x_1532_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___y_1412_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__43));
v___x_1534_ = l_Lean_Syntax_node1(v___y_1412_, v___x_1533_, v___y_1433_);
v___x_1535_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__45));
v___x_1536_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__47));
v___x_1537_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__49));
lean_inc_ref(v___y_1421_);
v___x_1538_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1538_, 0, v___y_1412_);
lean_ctor_set(v___x_1538_, 1, v___y_1421_);
lean_ctor_set(v___x_1538_, 2, v___y_1409_);
lean_ctor_set(v___x_1538_, 3, v___y_1429_);
v___x_1539_ = l_Lean_Syntax_node1(v___y_1412_, v___x_1537_, v___x_1538_);
lean_inc_ref_n(v___y_1423_, 5);
v___x_1540_ = l_String_toRawSubstring_x27(v___y_1423_);
v___x_1541_ = l_Lean_Name_mkStr1(v___y_1423_);
v___x_1542_ = l_Lean_addMacroScope(v___y_1427_, v___x_1541_, v___y_1438_);
lean_inc_ref_n(v___y_1407_, 2);
lean_inc_ref_n(v___y_1434_, 2);
v___x_1543_ = l_Lean_Name_mkStr4(v___x_1401_, v___y_1434_, v___y_1407_, v___y_1423_);
lean_inc(v___x_1543_);
v___x_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v___y_1436_);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
v___x_1546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___y_1429_);
v___x_1547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1544_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1548_, 0, v___y_1412_);
lean_ctor_set(v___x_1548_, 1, v___x_1540_);
lean_ctor_set(v___x_1548_, 2, v___x_1542_);
lean_ctor_set(v___x_1548_, 3, v___x_1547_);
v___x_1549_ = l_Lean_Syntax_node2(v___y_1412_, v___y_1432_, v___x_1548_, v___x_1518_);
v___x_1550_ = l_Lean_Syntax_node2(v___y_1412_, v___x_1517_, v___x_1467_, v___x_1549_);
v___x_1551_ = l_Lean_Syntax_node1(v___y_1412_, v___y_1418_, v___x_1550_);
v___x_1552_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__51));
v___x_1553_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__52));
v___x_1554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___y_1412_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = l_Lean_Syntax_node2(v___y_1412_, v___x_1552_, v___x_1554_, v___y_1431_);
v___x_1556_ = l_Array_append___redArg(v___y_1435_, v___y_1430_);
lean_dec_ref(v___y_1430_);
v___x_1557_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1557_, 0, v___y_1412_);
lean_ctor_set(v___x_1557_, 1, v___y_1418_);
lean_ctor_set(v___x_1557_, 2, v___x_1556_);
v___x_1558_ = l_Lean_Syntax_node2(v___y_1412_, v___y_1432_, v___x_1555_, v___x_1557_);
v___x_1559_ = l_Lean_Syntax_node5(v___y_1412_, v___x_1536_, v___x_1539_, v___y_1433_, v___x_1551_, v___x_1483_, v___x_1558_);
v___x_1560_ = l_Lean_Syntax_node1(v___y_1412_, v___x_1535_, v___x_1559_);
lean_inc(v___x_1534_);
lean_inc_ref(v___x_1532_);
v___x_1561_ = l_Lean_Syntax_node4(v___y_1412_, v___x_1530_, v___x_1532_, v___y_1433_, v___x_1534_, v___x_1560_);
v___x_1562_ = l_Lean_Syntax_node2(v___y_1412_, v___x_1529_, v___x_1561_, v___y_1433_);
lean_inc_ref(v___y_1426_);
v___x_1563_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1563_, 0, v___y_1412_);
lean_ctor_set(v___x_1563_, 1, v___y_1426_);
lean_ctor_set(v___x_1563_, 2, v___y_1419_);
lean_ctor_set(v___x_1563_, 3, v___y_1429_);
v___x_1564_ = l_Lean_Syntax_node1(v___y_1412_, v___x_1537_, v___x_1563_);
v___x_1565_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__54);
v___x_1566_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__55));
v___x_1567_ = l_Lean_Name_mkStr2(v___y_1423_, v___x_1566_);
v___x_1568_ = l_Lean_addMacroScope(v___y_1427_, v___x_1567_, v___y_1438_);
v___x_1569_ = l_Lean_Name_mkStr5(v___x_1401_, v___y_1434_, v___y_1407_, v___y_1423_, v___x_1566_);
v___x_1570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
lean_ctor_set(v___x_1570_, 1, v___y_1436_);
v___x_1571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___y_1429_);
v___x_1572_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1572_, 0, v___y_1412_);
lean_ctor_set(v___x_1572_, 1, v___x_1565_);
lean_ctor_set(v___x_1572_, 2, v___x_1568_);
lean_ctor_set(v___x_1572_, 3, v___x_1571_);
v___x_1573_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__57);
v___x_1574_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__58));
v___x_1575_ = l_Lean_addMacroScope(v___y_1427_, v___x_1574_, v___y_1438_);
v___x_1576_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1576_, 0, v___y_1412_);
lean_ctor_set(v___x_1576_, 1, v___x_1573_);
lean_ctor_set(v___x_1576_, 2, v___x_1575_);
lean_ctor_set(v___x_1576_, 3, v___y_1429_);
v___x_1577_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__60);
v___x_1578_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__61));
v___x_1579_ = l_Lean_addMacroScope(v___y_1427_, v___x_1578_, v___y_1438_);
v___x_1580_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__62));
v___x_1581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v___y_1436_);
v___x_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v___y_1429_);
v___x_1583_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1583_, 0, v___y_1412_);
lean_ctor_set(v___x_1583_, 1, v___x_1577_);
lean_ctor_set(v___x_1583_, 2, v___x_1579_);
lean_ctor_set(v___x_1583_, 3, v___x_1582_);
v___x_1584_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__64));
v___x_1585_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__65));
v___x_1586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___y_1412_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
lean_inc_ref(v___x_1586_);
v___x_1587_ = l_Lean_Syntax_node3(v___y_1412_, v___x_1584_, v___x_1586_, v___x_1586_, v_type_1394_);
v___x_1588_ = l_Lean_Syntax_node1(v___y_1412_, v___y_1418_, v___x_1587_);
v___x_1589_ = l_Lean_Syntax_node2(v___y_1412_, v___y_1432_, v___x_1583_, v___x_1588_);
v___x_1590_ = l_Lean_Syntax_node5(v___y_1412_, v___y_1424_, v___x_1464_, v___x_1576_, v___x_1483_, v___x_1589_, v___x_1477_);
v___x_1591_ = l_Lean_Syntax_node1(v___y_1412_, v___y_1418_, v___x_1590_);
v___x_1592_ = l_Lean_Syntax_node2(v___y_1412_, v___y_1432_, v___x_1572_, v___x_1591_);
v___x_1593_ = l_Lean_Syntax_node5(v___y_1412_, v___x_1536_, v___x_1564_, v___y_1433_, v___y_1433_, v___x_1483_, v___x_1592_);
v___x_1594_ = l_Lean_Syntax_node1(v___y_1412_, v___x_1535_, v___x_1593_);
v___x_1595_ = l_Lean_Syntax_node4(v___y_1412_, v___x_1530_, v___x_1532_, v___y_1433_, v___x_1534_, v___x_1594_);
v___x_1596_ = l_Lean_Syntax_node2(v___y_1412_, v___x_1529_, v___x_1595_, v___y_1433_);
v___x_1597_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__67));
v___x_1598_ = l_Lean_Syntax_node1(v___y_1412_, v___x_1597_, v___y_1417_);
v___x_1599_ = l_Lean_Syntax_node2(v___y_1412_, v___x_1529_, v___x_1598_, v___y_1433_);
v___x_1600_ = l_Lean_Syntax_node3(v___y_1412_, v___y_1418_, v___x_1562_, v___x_1596_, v___x_1599_);
v___x_1601_ = l_Lean_Syntax_node1(v___y_1412_, v___x_1528_, v___x_1600_);
v___x_1602_ = l_Lean_Syntax_node2(v___y_1412_, v___x_1526_, v___x_1527_, v___x_1601_);
v___x_1603_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__70));
v___x_1604_ = l_Lean_Syntax_node2(v___y_1412_, v___x_1603_, v___y_1433_, v___y_1433_);
v___x_1605_ = l_Lean_Syntax_node4(v___y_1412_, v___x_1524_, v___x_1483_, v___x_1602_, v___x_1604_, v___y_1433_);
v___x_1606_ = l_Lean_Syntax_node5(v___y_1412_, v___x_1444_, v___x_1446_, v___x_1454_, v___x_1522_, v___x_1605_, v___y_1433_);
v___x_1607_ = l_Lean_Syntax_node2(v___y_1412_, v___y_1414_, v___x_1442_, v___x_1606_);
v___x_1608_ = l_Lean_Syntax_node2(v___y_1412_, v___y_1418_, v___y_1425_, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_ctor_set(v___x_1609_, 1, v___y_1410_);
return v___x_1609_;
}
v___jp_1610_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_inc_ref(v___y_1642_);
v___x_1646_ = l_Array_append___redArg(v___y_1642_, v___y_1645_);
lean_dec_ref(v___y_1645_);
lean_inc(v___y_1623_);
lean_inc(v___y_1619_);
v___x_1647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1647_, 0, v___y_1619_);
lean_ctor_set(v___x_1647_, 1, v___y_1623_);
lean_ctor_set(v___x_1647_, 2, v___x_1646_);
if (lean_obj_tag(v_vis_x3f_1391_) == 1)
{
lean_object* v_val_1648_; lean_object* v___x_1649_; 
v_val_1648_ = lean_ctor_get(v_vis_x3f_1391_, 0);
lean_inc(v_val_1648_);
lean_dec_ref_known(v_vis_x3f_1391_, 1);
v___x_1649_ = l_Array_mkArray1___redArg(v_val_1648_);
v___y_1404_ = v___y_1611_;
v___y_1405_ = v___y_1612_;
v___y_1406_ = v___y_1613_;
v___y_1407_ = v___y_1614_;
v___y_1408_ = v___y_1615_;
v___y_1409_ = v___y_1616_;
v___y_1410_ = v___y_1618_;
v___y_1411_ = v___y_1617_;
v___y_1412_ = v___y_1619_;
v___y_1413_ = v___x_1647_;
v___y_1414_ = v___y_1620_;
v___y_1415_ = v___y_1621_;
v___y_1416_ = v___y_1622_;
v___y_1417_ = v___y_1624_;
v___y_1418_ = v___y_1623_;
v___y_1419_ = v___y_1625_;
v___y_1420_ = v___y_1626_;
v___y_1421_ = v___y_1627_;
v___y_1422_ = v___y_1628_;
v___y_1423_ = v___y_1629_;
v___y_1424_ = v___y_1630_;
v___y_1425_ = v___y_1631_;
v___y_1426_ = v___y_1632_;
v___y_1427_ = v___y_1633_;
v___y_1428_ = v___y_1634_;
v___y_1429_ = v___y_1635_;
v___y_1430_ = v___y_1637_;
v___y_1431_ = v___y_1636_;
v___y_1432_ = v___y_1638_;
v___y_1433_ = v___y_1639_;
v___y_1434_ = v___y_1640_;
v___y_1435_ = v___y_1642_;
v___y_1436_ = v___y_1641_;
v___y_1437_ = v___y_1643_;
v___y_1438_ = v___y_1644_;
v___y_1439_ = v___x_1649_;
goto v___jp_1403_;
}
else
{
lean_object* v___x_1650_; 
lean_dec(v_vis_x3f_1391_);
v___x_1650_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___y_1404_ = v___y_1611_;
v___y_1405_ = v___y_1612_;
v___y_1406_ = v___y_1613_;
v___y_1407_ = v___y_1614_;
v___y_1408_ = v___y_1615_;
v___y_1409_ = v___y_1616_;
v___y_1410_ = v___y_1618_;
v___y_1411_ = v___y_1617_;
v___y_1412_ = v___y_1619_;
v___y_1413_ = v___x_1647_;
v___y_1414_ = v___y_1620_;
v___y_1415_ = v___y_1621_;
v___y_1416_ = v___y_1622_;
v___y_1417_ = v___y_1624_;
v___y_1418_ = v___y_1623_;
v___y_1419_ = v___y_1625_;
v___y_1420_ = v___y_1626_;
v___y_1421_ = v___y_1627_;
v___y_1422_ = v___y_1628_;
v___y_1423_ = v___y_1629_;
v___y_1424_ = v___y_1630_;
v___y_1425_ = v___y_1631_;
v___y_1426_ = v___y_1632_;
v___y_1427_ = v___y_1633_;
v___y_1428_ = v___y_1634_;
v___y_1429_ = v___y_1635_;
v___y_1430_ = v___y_1637_;
v___y_1431_ = v___y_1636_;
v___y_1432_ = v___y_1638_;
v___y_1433_ = v___y_1639_;
v___y_1434_ = v___y_1640_;
v___y_1435_ = v___y_1642_;
v___y_1436_ = v___y_1641_;
v___y_1437_ = v___y_1643_;
v___y_1438_ = v___y_1644_;
v___y_1439_ = v___x_1650_;
goto v___jp_1403_;
}
}
v___jp_1651_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_inc_ref(v___y_1686_);
v___x_1690_ = l_Array_append___redArg(v___y_1686_, v___y_1689_);
lean_dec_ref(v___y_1689_);
lean_inc(v___y_1663_);
lean_inc_n(v___y_1660_, 2);
v___x_1691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1691_, 0, v___y_1660_);
lean_ctor_set(v___x_1691_, 1, v___y_1663_);
lean_ctor_set(v___x_1691_, 2, v___x_1690_);
v___x_1692_ = lean_unsigned_to_nat(9u);
v___x_1693_ = lean_mk_empty_array_with_capacity(v___x_1692_);
lean_inc(v___y_1683_);
v___x_1694_ = lean_array_push(v___x_1693_, v___y_1683_);
v___x_1695_ = lean_array_push(v___x_1694_, v___y_1675_);
v___x_1696_ = lean_array_push(v___x_1695_, v___y_1679_);
v___x_1697_ = lean_array_push(v___x_1696_, v___y_1674_);
lean_inc(v___y_1681_);
v___x_1698_ = lean_array_push(v___x_1697_, v___y_1681_);
v___x_1699_ = lean_array_push(v___x_1698_, v___y_1668_);
v___x_1700_ = lean_array_push(v___x_1699_, v___y_1673_);
lean_inc(v_type_1394_);
v___x_1701_ = lean_array_push(v___x_1700_, v_type_1394_);
v___x_1702_ = lean_array_push(v___x_1701_, v___x_1691_);
lean_inc(v___y_1665_);
v___x_1703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1703_, 0, v___y_1660_);
lean_ctor_set(v___x_1703_, 1, v___y_1665_);
lean_ctor_set(v___x_1703_, 2, v___x_1702_);
v___x_1704_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__71));
lean_inc_ref_n(v___y_1656_, 2);
v___x_1705_ = l_Lean_Name_mkStr4(v___x_1401_, v___x_1402_, v___y_1656_, v___x_1704_);
v___x_1706_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__72));
v___x_1707_ = l_Lean_Name_mkStr4(v___x_1401_, v___x_1402_, v___y_1656_, v___x_1706_);
if (lean_obj_tag(v_doc_x3f_1390_) == 1)
{
lean_object* v_val_1708_; lean_object* v___x_1709_; 
v_val_1708_ = lean_ctor_get(v_doc_x3f_1390_, 0);
lean_inc(v_val_1708_);
lean_dec_ref_known(v_doc_x3f_1390_, 1);
v___x_1709_ = l_Array_mkArray1___redArg(v_val_1708_);
v___y_1611_ = v___y_1652_;
v___y_1612_ = v___y_1653_;
v___y_1613_ = v___y_1654_;
v___y_1614_ = v___y_1655_;
v___y_1615_ = v___y_1656_;
v___y_1616_ = v___y_1657_;
v___y_1617_ = v___y_1658_;
v___y_1618_ = v___y_1659_;
v___y_1619_ = v___y_1660_;
v___y_1620_ = v___x_1705_;
v___y_1621_ = v___y_1661_;
v___y_1622_ = v___y_1662_;
v___y_1623_ = v___y_1663_;
v___y_1624_ = v___y_1664_;
v___y_1625_ = v___y_1666_;
v___y_1626_ = v___y_1667_;
v___y_1627_ = v___y_1669_;
v___y_1628_ = v___y_1671_;
v___y_1629_ = v___y_1670_;
v___y_1630_ = v___y_1672_;
v___y_1631_ = v___x_1703_;
v___y_1632_ = v___y_1676_;
v___y_1633_ = v___y_1677_;
v___y_1634_ = v___x_1707_;
v___y_1635_ = v___y_1678_;
v___y_1636_ = v___y_1681_;
v___y_1637_ = v___y_1680_;
v___y_1638_ = v___y_1682_;
v___y_1639_ = v___y_1683_;
v___y_1640_ = v___y_1684_;
v___y_1641_ = v___y_1685_;
v___y_1642_ = v___y_1686_;
v___y_1643_ = v___y_1687_;
v___y_1644_ = v___y_1688_;
v___y_1645_ = v___x_1709_;
goto v___jp_1610_;
}
else
{
lean_object* v___x_1710_; 
lean_dec(v_doc_x3f_1390_);
v___x_1710_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
v___y_1611_ = v___y_1652_;
v___y_1612_ = v___y_1653_;
v___y_1613_ = v___y_1654_;
v___y_1614_ = v___y_1655_;
v___y_1615_ = v___y_1656_;
v___y_1616_ = v___y_1657_;
v___y_1617_ = v___y_1658_;
v___y_1618_ = v___y_1659_;
v___y_1619_ = v___y_1660_;
v___y_1620_ = v___x_1705_;
v___y_1621_ = v___y_1661_;
v___y_1622_ = v___y_1662_;
v___y_1623_ = v___y_1663_;
v___y_1624_ = v___y_1664_;
v___y_1625_ = v___y_1666_;
v___y_1626_ = v___y_1667_;
v___y_1627_ = v___y_1669_;
v___y_1628_ = v___y_1671_;
v___y_1629_ = v___y_1670_;
v___y_1630_ = v___y_1672_;
v___y_1631_ = v___x_1703_;
v___y_1632_ = v___y_1676_;
v___y_1633_ = v___y_1677_;
v___y_1634_ = v___x_1707_;
v___y_1635_ = v___y_1678_;
v___y_1636_ = v___y_1681_;
v___y_1637_ = v___y_1680_;
v___y_1638_ = v___y_1682_;
v___y_1639_ = v___y_1683_;
v___y_1640_ = v___y_1684_;
v___y_1641_ = v___y_1685_;
v___y_1642_ = v___y_1686_;
v___y_1643_ = v___y_1687_;
v___y_1644_ = v___y_1688_;
v___y_1645_ = v___x_1710_;
goto v___jp_1610_;
}
}
v___jp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__74));
v___x_1715_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__75);
lean_inc_ref(v_a_1397_);
v___x_1716_ = lean_apply_3(v_mkLogExceptionsTerm_1389_, v___x_1715_, v_a_1397_, v_a_1713_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1814_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_a_1718_ = lean_ctor_get(v___x_1716_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1720_ = v___x_1716_;
v_isShared_1721_ = v_isSharedCheck_1814_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1814_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v_quotContext_1722_; lean_object* v_currMacroScope_1723_; lean_object* v_ref_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1747_; 
v_quotContext_1722_ = lean_ctor_get(v_a_1397_, 1);
v_currMacroScope_1723_ = lean_ctor_get(v_a_1397_, 2);
v_ref_1724_ = lean_ctor_get(v_a_1397_, 5);
v___x_1725_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__78);
v___x_1726_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__81);
v___x_1727_ = 0;
v___x_1728_ = l_Lean_SourceInfo_fromRef(v_ref_1724_, v___x_1727_);
v___x_1729_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__83));
v___x_1730_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__85);
v___x_1731_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__86));
v___x_1732_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__88));
lean_inc_n(v_currMacroScope_1723_, 2);
lean_inc_n(v_quotContext_1722_, 2);
v___x_1733_ = l_Lean_addMacroScope(v_quotContext_1722_, v___x_1732_, v_currMacroScope_1723_);
v___x_1734_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__5));
v___x_1735_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__6));
v___x_1736_ = lean_box(0);
v___x_1737_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__91));
lean_inc_n(v___x_1728_, 3);
v___x_1738_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1728_);
lean_ctor_set(v___x_1738_, 1, v___x_1730_);
lean_ctor_set(v___x_1738_, 2, v___x_1733_);
lean_ctor_set(v___x_1738_, 3, v___x_1737_);
v___x_1739_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5));
v___x_1740_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__93);
v___x_1741_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__94));
v___x_1742_ = l_Lean_addMacroScope(v_quotContext_1722_, v___x_1741_, v_currMacroScope_1723_);
lean_inc(v___x_1742_);
v___x_1743_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1728_);
lean_ctor_set(v___x_1743_, 1, v___x_1740_);
lean_ctor_set(v___x_1743_, 2, v___x_1742_);
lean_ctor_set(v___x_1743_, 3, v___x_1736_);
v___x_1744_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__96));
v___x_1745_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97));
if (v_isShared_1721_ == 0)
{
lean_ctor_set_tag(v___x_1720_, 2);
lean_ctor_set(v___x_1720_, 1, v___x_1745_);
lean_ctor_set(v___x_1720_, 0, v___x_1728_);
v___x_1747_ = v___x_1720_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1748_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__99);
v___x_1749_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__100));
lean_inc_n(v_currMacroScope_1723_, 2);
lean_inc_n(v_quotContext_1722_, 2);
v___x_1750_ = l_Lean_addMacroScope(v_quotContext_1722_, v___x_1749_, v_currMacroScope_1723_);
lean_inc(v___x_1750_);
lean_inc_n(v___x_1728_, 7);
v___x_1751_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1728_);
lean_ctor_set(v___x_1751_, 1, v___x_1748_);
lean_ctor_set(v___x_1751_, 2, v___x_1750_);
lean_ctor_set(v___x_1751_, 3, v___x_1736_);
v___x_1752_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__101));
v___x_1753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1728_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102));
v___x_1755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1728_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
lean_inc_ref(v___x_1755_);
lean_inc_ref(v___x_1753_);
lean_inc_ref(v___x_1751_);
lean_inc_ref(v___x_1747_);
v___x_1756_ = l_Lean_Syntax_node5(v___x_1728_, v___x_1744_, v___x_1747_, v___x_1751_, v___x_1753_, v___x_1751_, v___x_1755_);
v___x_1757_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__103);
v___x_1758_ = l_Lean_addMacroScope(v_quotContext_1722_, v___x_1714_, v_currMacroScope_1723_);
v___x_1759_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1728_);
lean_ctor_set(v___x_1759_, 1, v___x_1757_);
lean_ctor_set(v___x_1759_, 2, v___x_1758_);
lean_ctor_set(v___x_1759_, 3, v___x_1736_);
v___x_1760_ = l_Lean_Syntax_node5(v___x_1728_, v___x_1744_, v___x_1747_, v___x_1759_, v___x_1753_, v_a_1717_, v___x_1755_);
v___x_1761_ = l_Lean_Syntax_node5(v___x_1728_, v___x_1739_, v___x_1743_, v___x_1726_, v___x_1725_, v___x_1756_, v___x_1760_);
v___x_1762_ = l_Lean_Syntax_node2(v___x_1728_, v___x_1729_, v___x_1738_, v___x_1761_);
lean_inc_ref(v_a_1397_);
v___x_1763_ = lean_apply_3(v_mkMonadAdapt_1387_, v___x_1762_, v_a_1397_, v_a_1718_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1812_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_a_1765_ = lean_ctor_get(v___x_1763_, 1);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1767_ = v___x_1763_;
v_isShared_1768_ = v_isSharedCheck_1812_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1812_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v_fnName_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v_ref_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1769_ = l_Lean_TSyntax_getId(v_elabName_1393_);
v___x_1770_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__105));
v___x_1771_ = l_Lean_Name_append(v___x_1769_, v___x_1770_);
v_fnName_1772_ = l_Lean_mkIdentFrom(v_elabName_1393_, v___x_1771_, v___x_1727_);
v___x_1773_ = lean_unsigned_to_nat(3u);
v___x_1774_ = lean_mk_empty_array_with_capacity(v___x_1773_);
v___x_1775_ = lean_array_push(v___x_1774_, v_tk_1392_);
lean_inc(v_elabName_1393_);
v___x_1776_ = lean_array_push(v___x_1775_, v_elabName_1393_);
lean_inc(v_type_1394_);
v___x_1777_ = lean_array_push(v___x_1776_, v_type_1394_);
v___x_1778_ = lean_box(2);
v___x_1779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v___x_1739_);
lean_ctor_set(v___x_1779_, 2, v___x_1777_);
v_ref_1780_ = l_Lean_replaceRef(v___x_1779_, v_ref_1724_);
lean_dec_ref_known(v___x_1779_, 3);
v___x_1781_ = l_Lean_SourceInfo_fromRef(v_ref_1780_, v___x_1727_);
lean_dec(v_ref_1780_);
v___x_1782_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__1));
v___x_1783_ = lean_obj_once(&l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6, &l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6_once, _init_l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__6);
lean_inc_n(v___x_1781_, 2);
v___x_1784_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1781_);
lean_ctor_set(v___x_1784_, 1, v___x_1739_);
lean_ctor_set(v___x_1784_, 2, v___x_1783_);
v___x_1785_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2));
v___x_1786_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__106));
v___x_1787_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__107));
if (v_isShared_1768_ == 0)
{
lean_ctor_set_tag(v___x_1767_, 2);
lean_ctor_set(v___x_1767_, 1, v___x_1786_);
lean_ctor_set(v___x_1767_, 0, v___x_1781_);
v___x_1789_ = v___x_1767_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v___x_1786_);
v___x_1789_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; size_t v_sz_1801_; size_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_inc_n(v___x_1781_, 9);
v___x_1790_ = l_Lean_Syntax_node1(v___x_1781_, v___x_1787_, v___x_1789_);
v___x_1791_ = l_Lean_Syntax_node1(v___x_1781_, v___x_1739_, v___x_1790_);
v___x_1792_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabEnsureEvalTermInstance___closed__4));
v___x_1793_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__108));
v___x_1794_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__109));
v___x_1795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1781_);
lean_ctor_set(v___x_1795_, 1, v___x_1793_);
v___x_1796_ = l_Lean_Syntax_node1(v___x_1781_, v___x_1794_, v___x_1795_);
v___x_1797_ = l_Lean_Syntax_node1(v___x_1781_, v___x_1739_, v___x_1796_);
v___x_1798_ = l_Lean_Syntax_node1(v___x_1781_, v___x_1792_, v___x_1797_);
v___x_1799_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__110));
v___x_1800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1781_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v_sz_1801_ = lean_array_size(v_binders_1395_);
v___x_1802_ = ((size_t)0ULL);
lean_inc_ref(v_binders_1395_);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd_spec__0(v_sz_1801_, v___x_1802_, v_binders_1395_);
v___x_1804_ = l_Array_append___redArg(v___x_1783_, v___x_1803_);
lean_dec_ref(v___x_1803_);
v___x_1805_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1781_);
lean_ctor_set(v___x_1805_, 1, v___x_1739_);
lean_ctor_set(v___x_1805_, 2, v___x_1804_);
v___x_1806_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__111));
v___x_1807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1781_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
if (lean_obj_tag(v_entries_x3f_1396_) == 1)
{
lean_object* v_val_1808_; lean_object* v___x_1809_; 
v_val_1808_ = lean_ctor_get(v_entries_x3f_1396_, 0);
lean_inc(v_val_1808_);
lean_dec_ref_known(v_entries_x3f_1396_, 1);
v___x_1809_ = l_Array_mkArray1___redArg(v_val_1808_);
lean_inc(v_currMacroScope_1723_);
lean_inc(v_quotContext_1722_);
v___y_1652_ = v___x_1754_;
v___y_1653_ = v___x_1778_;
v___y_1654_ = v___x_1715_;
v___y_1655_ = v___x_1735_;
v___y_1656_ = v___x_1785_;
v___y_1657_ = v___x_1742_;
v___y_1658_ = v___x_1752_;
v___y_1659_ = v_a_1765_;
v___y_1660_ = v___x_1781_;
v___y_1661_ = v___x_1802_;
v___y_1662_ = v___x_1725_;
v___y_1663_ = v___x_1739_;
v___y_1664_ = v_a_1764_;
v___y_1665_ = v___x_1782_;
v___y_1666_ = v___x_1750_;
v___y_1667_ = v_sz_1801_;
v___y_1668_ = v___x_1805_;
v___y_1669_ = v___x_1740_;
v___y_1670_ = v___x_1731_;
v___y_1671_ = v___x_1726_;
v___y_1672_ = v___x_1744_;
v___y_1673_ = v___x_1807_;
v___y_1674_ = v___x_1800_;
v___y_1675_ = v___x_1791_;
v___y_1676_ = v___x_1748_;
v___y_1677_ = v_quotContext_1722_;
v___y_1678_ = v___x_1736_;
v___y_1679_ = v___x_1798_;
v___y_1680_ = v_a_1712_;
v___y_1681_ = v_fnName_1772_;
v___y_1682_ = v___x_1729_;
v___y_1683_ = v___x_1784_;
v___y_1684_ = v___x_1734_;
v___y_1685_ = v___x_1736_;
v___y_1686_ = v___x_1783_;
v___y_1687_ = v___x_1745_;
v___y_1688_ = v_currMacroScope_1723_;
v___y_1689_ = v___x_1809_;
goto v___jp_1651_;
}
else
{
lean_object* v___x_1810_; 
lean_dec(v_entries_x3f_1396_);
v___x_1810_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__7));
lean_inc(v_currMacroScope_1723_);
lean_inc(v_quotContext_1722_);
v___y_1652_ = v___x_1754_;
v___y_1653_ = v___x_1778_;
v___y_1654_ = v___x_1715_;
v___y_1655_ = v___x_1735_;
v___y_1656_ = v___x_1785_;
v___y_1657_ = v___x_1742_;
v___y_1658_ = v___x_1752_;
v___y_1659_ = v_a_1765_;
v___y_1660_ = v___x_1781_;
v___y_1661_ = v___x_1802_;
v___y_1662_ = v___x_1725_;
v___y_1663_ = v___x_1739_;
v___y_1664_ = v_a_1764_;
v___y_1665_ = v___x_1782_;
v___y_1666_ = v___x_1750_;
v___y_1667_ = v_sz_1801_;
v___y_1668_ = v___x_1805_;
v___y_1669_ = v___x_1740_;
v___y_1670_ = v___x_1731_;
v___y_1671_ = v___x_1726_;
v___y_1672_ = v___x_1744_;
v___y_1673_ = v___x_1807_;
v___y_1674_ = v___x_1800_;
v___y_1675_ = v___x_1791_;
v___y_1676_ = v___x_1748_;
v___y_1677_ = v_quotContext_1722_;
v___y_1678_ = v___x_1736_;
v___y_1679_ = v___x_1798_;
v___y_1680_ = v_a_1712_;
v___y_1681_ = v_fnName_1772_;
v___y_1682_ = v___x_1729_;
v___y_1683_ = v___x_1784_;
v___y_1684_ = v___x_1734_;
v___y_1685_ = v___x_1736_;
v___y_1686_ = v___x_1783_;
v___y_1687_ = v___x_1745_;
v___y_1688_ = v_currMacroScope_1723_;
v___y_1689_ = v___x_1810_;
goto v___jp_1651_;
}
}
}
}
else
{
lean_dec(v___x_1750_);
lean_dec(v___x_1742_);
lean_dec_ref(v_a_1712_);
lean_dec(v_entries_x3f_1396_);
lean_dec_ref(v_binders_1395_);
lean_dec(v_type_1394_);
lean_dec(v_elabName_1393_);
lean_dec(v_tk_1392_);
lean_dec(v_vis_x3f_1391_);
lean_dec(v_doc_x3f_1390_);
lean_dec(v_logExceptionsDefault_1388_);
lean_dec(v_monad_1386_);
return v___x_1763_;
}
}
}
}
else
{
lean_dec_ref(v_a_1712_);
lean_dec(v_entries_x3f_1396_);
lean_dec_ref(v_binders_1395_);
lean_dec(v_type_1394_);
lean_dec(v_elabName_1393_);
lean_dec(v_tk_1392_);
lean_dec(v_vis_x3f_1391_);
lean_dec(v_doc_x3f_1390_);
lean_dec(v_logExceptionsDefault_1388_);
lean_dec_ref(v_mkMonadAdapt_1387_);
lean_dec(v_monad_1386_);
return v___x_1716_;
}
}
v___jp_1815_:
{
if (lean_obj_tag(v___y_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v_a_1818_; 
v_a_1817_ = lean_ctor_get(v___y_1816_, 0);
lean_inc(v_a_1817_);
v_a_1818_ = lean_ctor_get(v___y_1816_, 1);
lean_inc(v_a_1818_);
lean_dec_ref_known(v___y_1816_, 2);
v_a_1712_ = v_a_1817_;
v_a_1713_ = v_a_1818_;
goto v___jp_1711_;
}
else
{
lean_object* v_a_1819_; lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_entries_x3f_1396_);
lean_dec_ref(v_binders_1395_);
lean_dec(v_type_1394_);
lean_dec(v_elabName_1393_);
lean_dec(v_tk_1392_);
lean_dec(v_vis_x3f_1391_);
lean_dec(v_doc_x3f_1390_);
lean_dec_ref(v_mkLogExceptionsTerm_1389_);
lean_dec(v_logExceptionsDefault_1388_);
lean_dec_ref(v_mkMonadAdapt_1387_);
lean_dec(v_monad_1386_);
v_a_1819_ = lean_ctor_get(v___y_1816_, 0);
v_a_1820_ = lean_ctor_get(v___y_1816_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___y_1816_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___y_1816_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_inc(v_a_1819_);
lean_dec(v___y_1816_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1819_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___boxed(lean_object* v_monad_1837_, lean_object* v_mkMonadAdapt_1838_, lean_object* v_logExceptionsDefault_1839_, lean_object* v_mkLogExceptionsTerm_1840_, lean_object* v_doc_x3f_1841_, lean_object* v_vis_x3f_1842_, lean_object* v_tk_1843_, lean_object* v_elabName_1844_, lean_object* v_type_1845_, lean_object* v_binders_1846_, lean_object* v_entries_x3f_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v_monad_1837_, v_mkMonadAdapt_1838_, v_logExceptionsDefault_1839_, v_mkLogExceptionsTerm_1840_, v_doc_x3f_1841_, v_vis_x3f_1842_, v_tk_1843_, v_elabName_1844_, v_type_1845_, v_binders_1846_, v_entries_x3f_1847_, v_a_1848_, v_a_1849_);
lean_dec_ref(v_a_1848_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0(lean_object* v_logExceptions_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v_logExceptions_1851_);
lean_ctor_set(v___x_1854_, 1, v___y_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0___boxed(lean_object* v_logExceptions_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__0(v_logExceptions_1855_, v___y_1856_, v___y_1857_);
lean_dec_ref(v___y_1856_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1(lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___y_1859_);
lean_ctor_set(v___x_1862_, 1, v___y_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1___boxed(lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___lam__1(v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec_ref(v___y_1864_);
return v_res_1866_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__6));
v___x_1882_ = l_Lean_mkCIdent(v___x_1881_);
return v___x_1882_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__9));
v___x_1888_ = l_Lean_mkCIdent(v___x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab(lean_object* v_x_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1892_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1));
lean_inc(v_x_1889_);
v___x_1893_ = l_Lean_Syntax_isOfKind(v_x_1889_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; 
lean_dec(v_x_1889_);
v___x_1894_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1891_);
return v___x_1894_;
}
else
{
lean_object* v___f_1895_; lean_object* v___f_1896_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v_entries_x3f_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___x_1940_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v_vis_x3f_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v_doc_x3f_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___f_1895_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2));
v___f_1896_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3));
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1982_ = l_Lean_Syntax_getArg(v_x_1889_, v___x_1940_);
v___x_1983_ = l_Lean_Syntax_isNone(v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1984_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1982_);
v___x_1985_ = l_Lean_Syntax_matchesNull(v___x_1982_, v___x_1984_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; 
lean_dec(v___x_1982_);
lean_dec(v_x_1889_);
v___x_1986_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1891_);
return v___x_1986_;
}
else
{
lean_object* v_doc_x3f_1987_; 
v_doc_x3f_1987_ = l_Lean_Syntax_getArg(v___x_1982_, v___x_1940_);
lean_dec(v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1990_; uint8_t v___x_1991_; 
v___x_1990_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_1987_);
v___x_1991_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1987_, v___x_1990_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; 
lean_dec(v_doc_x3f_1987_);
lean_dec(v_x_1889_);
v___x_1992_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1891_);
return v___x_1992_;
}
else
{
goto v___jp_1988_;
}
}
else
{
goto v___jp_1988_;
}
v___jp_1988_:
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1989_, 0, v_doc_x3f_1987_);
v_doc_x3f_1971_ = v___x_1989_;
v___y_1972_ = v_a_1890_;
v___y_1973_ = v_a_1891_;
goto v___jp_1970_;
}
}
}
else
{
lean_object* v___x_1993_; 
lean_dec(v___x_1982_);
v___x_1993_ = lean_box(0);
v_doc_x3f_1971_ = v___x_1993_;
v___y_1972_ = v_a_1890_;
v___y_1973_ = v_a_1891_;
goto v___jp_1970_;
}
v___jp_1897_:
{
lean_object* v_binders_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_binders_1907_ = l_Lean_Syntax_getArgs(v___y_1900_);
lean_dec(v___y_1900_);
v___x_1908_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7, &l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7_once, _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__7);
v___x_1909_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10, &l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10_once, _init_l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__10);
v___x_1910_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_1908_, v___f_1896_, v___x_1909_, v___f_1895_, v___y_1898_, v___y_1903_, v___y_1901_, v___y_1902_, v___y_1899_, v_binders_1907_, v_entries_x3f_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_a_1912_ = lean_ctor_get(v___x_1910_, 1);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1910_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1911_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
v_a_1920_ = lean_ctor_get(v___x_1910_, 0);
v_a_1921_ = lean_ctor_get(v___x_1910_, 1);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1910_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_inc(v_a_1920_);
lean_dec(v___x_1910_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1920_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
v___jp_1929_:
{
lean_object* v___x_1939_; 
v___x_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___y_1931_);
v___y_1898_ = v___y_1930_;
v___y_1899_ = v___y_1932_;
v___y_1900_ = v___y_1933_;
v___y_1901_ = v___y_1934_;
v___y_1902_ = v___y_1937_;
v___y_1903_ = v___y_1936_;
v_entries_x3f_1904_ = v___x_1939_;
v___y_1905_ = v___y_1938_;
v___y_1906_ = v___y_1935_;
goto v___jp_1897_;
}
v___jp_1941_:
{
lean_object* v___x_1947_; lean_object* v_elabName_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1947_ = lean_unsigned_to_nat(3u);
v_elabName_1948_ = l_Lean_Syntax_getArg(v_x_1889_, v___x_1947_);
v___x_1949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_elabName_1948_);
v___x_1950_ = l_Lean_Syntax_isOfKind(v_elabName_1948_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; 
lean_dec(v_elabName_1948_);
lean_dec(v_vis_x3f_1944_);
lean_dec(v___y_1942_);
lean_dec(v_x_1889_);
v___x_1951_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1946_);
return v___x_1951_;
}
else
{
lean_object* v___x_1952_; lean_object* v_type_1953_; uint8_t v___x_1954_; 
v___x_1952_ = lean_unsigned_to_nat(4u);
v_type_1953_ = l_Lean_Syntax_getArg(v_x_1889_, v___x_1952_);
lean_inc(v_type_1953_);
v___x_1954_ = l_Lean_Syntax_isOfKind(v_type_1953_, v___x_1949_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; 
lean_dec(v_type_1953_);
lean_dec(v_elabName_1948_);
lean_dec(v_vis_x3f_1944_);
lean_dec(v___y_1942_);
lean_dec(v_x_1889_);
v___x_1955_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1946_);
return v___x_1955_;
}
else
{
lean_object* v___x_1956_; lean_object* v_tk_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1956_ = lean_unsigned_to_nat(2u);
v_tk_1957_ = l_Lean_Syntax_getArg(v_x_1889_, v___x_1956_);
v___x_1958_ = lean_unsigned_to_nat(5u);
v___x_1959_ = l_Lean_Syntax_getArg(v_x_1889_, v___x_1958_);
v___x_1960_ = lean_unsigned_to_nat(6u);
v___x_1961_ = l_Lean_Syntax_getArg(v_x_1889_, v___x_1960_);
lean_dec(v_x_1889_);
v___x_1962_ = l_Lean_Syntax_isNone(v___x_1961_);
if (v___x_1962_ == 0)
{
uint8_t v___x_1963_; 
lean_inc(v___x_1961_);
v___x_1963_ = l_Lean_Syntax_matchesNull(v___x_1961_, v___y_1943_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; 
lean_dec(v___x_1961_);
lean_dec(v___x_1959_);
lean_dec(v_tk_1957_);
lean_dec(v_type_1953_);
lean_dec(v_elabName_1948_);
lean_dec(v_vis_x3f_1944_);
lean_dec(v___y_1942_);
v___x_1964_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1946_);
return v___x_1964_;
}
else
{
lean_object* v_entries_x3f_1965_; 
v_entries_x3f_1965_ = l_Lean_Syntax_getArg(v___x_1961_, v___x_1940_);
lean_dec(v___x_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1966_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_1965_);
v___x_1967_ = l_Lean_Syntax_isOfKind(v_entries_x3f_1965_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; 
lean_dec(v_entries_x3f_1965_);
lean_dec(v___x_1959_);
lean_dec(v_tk_1957_);
lean_dec(v_type_1953_);
lean_dec(v_elabName_1948_);
lean_dec(v_vis_x3f_1944_);
lean_dec(v___y_1942_);
v___x_1968_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1946_);
return v___x_1968_;
}
else
{
v___y_1930_ = v___y_1942_;
v___y_1931_ = v_entries_x3f_1965_;
v___y_1932_ = v_type_1953_;
v___y_1933_ = v___x_1959_;
v___y_1934_ = v_tk_1957_;
v___y_1935_ = v___y_1946_;
v___y_1936_ = v_vis_x3f_1944_;
v___y_1937_ = v_elabName_1948_;
v___y_1938_ = v___y_1945_;
goto v___jp_1929_;
}
}
else
{
v___y_1930_ = v___y_1942_;
v___y_1931_ = v_entries_x3f_1965_;
v___y_1932_ = v_type_1953_;
v___y_1933_ = v___x_1959_;
v___y_1934_ = v_tk_1957_;
v___y_1935_ = v___y_1946_;
v___y_1936_ = v_vis_x3f_1944_;
v___y_1937_ = v_elabName_1948_;
v___y_1938_ = v___y_1945_;
goto v___jp_1929_;
}
}
}
else
{
lean_object* v___x_1969_; 
lean_dec(v___x_1961_);
v___x_1969_ = lean_box(0);
v___y_1898_ = v___y_1942_;
v___y_1899_ = v_type_1953_;
v___y_1900_ = v___x_1959_;
v___y_1901_ = v_tk_1957_;
v___y_1902_ = v_elabName_1948_;
v___y_1903_ = v_vis_x3f_1944_;
v_entries_x3f_1904_ = v___x_1969_;
v___y_1905_ = v___y_1945_;
v___y_1906_ = v___y_1946_;
goto v___jp_1897_;
}
}
}
}
v___jp_1970_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1974_ = lean_unsigned_to_nat(1u);
v___x_1975_ = l_Lean_Syntax_getArg(v_x_1889_, v___x_1974_);
v___x_1976_ = l_Lean_Syntax_isNone(v___x_1975_);
if (v___x_1976_ == 0)
{
uint8_t v___x_1977_; 
lean_inc(v___x_1975_);
v___x_1977_ = l_Lean_Syntax_matchesNull(v___x_1975_, v___x_1974_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec(v___x_1975_);
lean_dec(v_doc_x3f_1971_);
lean_dec(v_x_1889_);
v___x_1978_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1973_);
return v___x_1978_;
}
else
{
lean_object* v_vis_x3f_1979_; lean_object* v___x_1980_; 
v_vis_x3f_1979_ = l_Lean_Syntax_getArg(v___x_1975_, v___x_1940_);
lean_dec(v___x_1975_);
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v_vis_x3f_1979_);
v___y_1942_ = v_doc_x3f_1971_;
v___y_1943_ = v___x_1974_;
v_vis_x3f_1944_ = v___x_1980_;
v___y_1945_ = v___y_1972_;
v___y_1946_ = v___y_1973_;
goto v___jp_1941_;
}
}
else
{
lean_object* v___x_1981_; 
lean_dec(v___x_1975_);
v___x_1981_ = lean_box(0);
v___y_1942_ = v_doc_x3f_1971_;
v___y_1943_ = v___x_1974_;
v_vis_x3f_1944_ = v___x_1981_;
v___y_1945_ = v___y_1972_;
v___y_1946_ = v___y_1973_;
goto v___jp_1941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___boxed(lean_object* v_x_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab(v_x_1994_, v_a_1995_, v_a_1996_);
lean_dec_ref(v_a_1995_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1(){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2005_ = l_Lean_Elab_macroAttribute;
v___x_2006_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1));
v___x_2007_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___closed__1));
v___x_2008_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___boxed), 3, 0);
v___x_2009_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2005_, v___x_2006_, v___x_2007_, v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1___boxed(lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab__1();
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab(lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2016_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_2017_ = lean_unsigned_to_nat(2u);
v___x_2018_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_2016_, v___x_2017_, v_a_2012_, v_a_2013_, v_a_2014_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___boxed(lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab(v_a_2019_, v_a_2020_, v_a_2021_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_a_2019_);
return v_res_2023_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___boxed), 4, 0);
v___x_2025_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_2025_, 0, v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1(){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2027_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__1));
v___x_2028_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___closed__0);
v___x_2029_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_2027_, v___x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1___boxed(lean_object* v_a_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareCoreConfigElab__1();
return v_res_2031_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__8));
v___x_2044_ = l_String_toRawSubstring_x27(v___x_2043_);
return v___x_2044_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__13));
v___x_2050_ = l_String_toRawSubstring_x27(v___x_2049_);
return v___x_2050_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__21));
v___x_2066_ = l_String_toRawSubstring_x27(v___x_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1(lean_object* v___x_2069_, lean_object* v___x_2070_, lean_object* v___x_2071_, lean_object* v___x_2072_, lean_object* v___x_2073_, lean_object* v_logExceptions_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_quotContext_2077_; lean_object* v_currMacroScope_2078_; lean_object* v_ref_2079_; uint8_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v_quotContext_2077_ = lean_ctor_get(v___y_2075_, 1);
v_currMacroScope_2078_ = lean_ctor_get(v___y_2075_, 2);
v_ref_2079_ = lean_ctor_get(v___y_2075_, 5);
v___x_2080_ = 0;
v___x_2081_ = l_Lean_SourceInfo_fromRef(v_ref_2079_, v___x_2080_);
v___x_2082_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1));
v___x_2083_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2));
lean_inc_n(v___x_2081_, 14);
v___x_2084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2081_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3));
lean_inc_ref_n(v___x_2071_, 5);
lean_inc_ref_n(v___x_2070_, 4);
lean_inc_ref_n(v___x_2069_, 9);
v___x_2086_ = l_Lean_Name_mkStr4(v___x_2069_, v___x_2070_, v___x_2071_, v___x_2085_);
v___x_2087_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4));
v___x_2088_ = l_Lean_Name_mkStr4(v___x_2069_, v___x_2070_, v___x_2071_, v___x_2087_);
v___x_2089_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5));
v___x_2090_ = l_Lean_Name_mkStr4(v___x_2069_, v___x_2070_, v___x_2071_, v___x_2089_);
v___x_2091_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97));
v___x_2092_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2081_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7));
v___x_2094_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9);
v___x_2095_ = lean_box(0);
lean_inc_n(v_currMacroScope_2078_, 3);
lean_inc_n(v_quotContext_2077_, 3);
v___x_2096_ = l_Lean_addMacroScope(v_quotContext_2077_, v___x_2095_, v_currMacroScope_2078_);
lean_inc_ref_n(v___x_2072_, 2);
v___x_2097_ = l_Lean_Name_mkStr3(v___x_2069_, v___x_2072_, v___x_2073_);
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
v___x_2099_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10));
v___x_2100_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2));
v___x_2101_ = l_Lean_Name_mkStr3(v___x_2069_, v___x_2099_, v___x_2100_);
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
v___x_2103_ = l_Lean_Name_mkStr3(v___x_2069_, v___x_2072_, v___x_2100_);
v___x_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
v___x_2105_ = l_Lean_Name_mkStr3(v___x_2069_, v___x_2072_, v___x_2071_);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
v___x_2107_ = l_Lean_Name_mkStr2(v___x_2069_, v___x_2099_);
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
v___x_2109_ = lean_box(0);
v___x_2110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2106_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2104_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2102_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2098_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2081_);
lean_ctor_set(v___x_2115_, 1, v___x_2094_);
lean_ctor_set(v___x_2115_, 2, v___x_2096_);
lean_ctor_set(v___x_2115_, 3, v___x_2114_);
v___x_2116_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2093_, v___x_2115_);
v___x_2117_ = l_Lean_Syntax_node2(v___x_2081_, v___x_2090_, v___x_2092_, v___x_2116_);
v___x_2118_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11));
v___x_2119_ = l_Lean_Name_mkStr4(v___x_2069_, v___x_2070_, v___x_2071_, v___x_2118_);
v___x_2120_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12));
v___x_2121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2081_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66));
v___x_2123_ = l_Lean_Name_mkStr4(v___x_2069_, v___x_2070_, v___x_2071_, v___x_2122_);
v___x_2124_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14);
v___x_2125_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15));
v___x_2126_ = l_Lean_addMacroScope(v_quotContext_2077_, v___x_2125_, v_currMacroScope_2078_);
v___x_2127_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19));
v___x_2128_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2081_);
lean_ctor_set(v___x_2128_, 1, v___x_2124_);
lean_ctor_set(v___x_2128_, 2, v___x_2126_);
lean_ctor_set(v___x_2128_, 3, v___x_2127_);
v___x_2129_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2123_, v___x_2128_);
v___x_2130_ = l_Lean_Syntax_node2(v___x_2081_, v___x_2119_, v___x_2121_, v___x_2129_);
v___x_2131_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102));
v___x_2132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2081_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = l_Lean_Syntax_node3(v___x_2081_, v___x_2088_, v___x_2117_, v___x_2130_, v___x_2132_);
v___x_2134_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20));
v___x_2135_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2081_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__22);
v___x_2137_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__23));
v___x_2138_ = l_Lean_addMacroScope(v_quotContext_2077_, v___x_2137_, v_currMacroScope_2078_);
v___x_2139_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2081_);
lean_ctor_set(v___x_2139_, 1, v___x_2136_);
lean_ctor_set(v___x_2139_, 2, v___x_2138_);
lean_ctor_set(v___x_2139_, 3, v___x_2109_);
v___x_2140_ = l_Lean_Syntax_node3(v___x_2081_, v___x_2086_, v___x_2133_, v___x_2135_, v___x_2139_);
v___x_2141_ = l_Lean_Syntax_node3(v___x_2081_, v___x_2082_, v_logExceptions_2074_, v___x_2084_, v___x_2140_);
v___x_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
lean_ctor_set(v___x_2142_, 1, v___y_2076_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___boxed(lean_object* v___x_2143_, lean_object* v___x_2144_, lean_object* v___x_2145_, lean_object* v___x_2146_, lean_object* v___x_2147_, lean_object* v_logExceptions_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1(v___x_2143_, v___x_2144_, v___x_2145_, v___x_2146_, v___x_2147_, v_logExceptions_2148_, v___y_2149_, v___y_2150_);
lean_dec_ref(v___y_2149_);
return v_res_2151_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__4));
v___x_2171_ = l_Lean_mkCIdent(v___x_2170_);
return v___x_2171_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__7));
v___x_2177_ = l_Lean_mkCIdent(v___x_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab(lean_object* v_x_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1));
lean_inc(v_x_2178_);
v___x_2182_ = l_Lean_Syntax_isOfKind(v_x_2178_, v___x_2181_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; 
lean_dec(v_x_2178_);
v___x_2183_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2180_);
return v___x_2183_;
}
else
{
lean_object* v___f_2184_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v_entries_x3f_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___x_2229_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v_vis_x3f_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v_doc_x3f_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___f_2184_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3));
v___x_2229_ = lean_unsigned_to_nat(0u);
v___x_2271_ = l_Lean_Syntax_getArg(v_x_2178_, v___x_2229_);
v___x_2272_ = l_Lean_Syntax_isNone(v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2271_);
v___x_2274_ = l_Lean_Syntax_matchesNull(v___x_2271_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; 
lean_dec(v___x_2271_);
lean_dec(v_x_2178_);
v___x_2275_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2180_);
return v___x_2275_;
}
else
{
lean_object* v_doc_x3f_2276_; 
v_doc_x3f_2276_ = l_Lean_Syntax_getArg(v___x_2271_, v___x_2229_);
lean_dec(v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2279_; uint8_t v___x_2280_; 
v___x_2279_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_2276_);
v___x_2280_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2276_, v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; 
lean_dec(v_doc_x3f_2276_);
lean_dec(v_x_2178_);
v___x_2281_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2180_);
return v___x_2281_;
}
else
{
goto v___jp_2277_;
}
}
else
{
goto v___jp_2277_;
}
v___jp_2277_:
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2278_, 0, v_doc_x3f_2276_);
v_doc_x3f_2260_ = v___x_2278_;
v___y_2261_ = v_a_2179_;
v___y_2262_ = v_a_2180_;
goto v___jp_2259_;
}
}
}
else
{
lean_object* v___x_2282_; 
lean_dec(v___x_2271_);
v___x_2282_ = lean_box(0);
v_doc_x3f_2260_ = v___x_2282_;
v___y_2261_ = v_a_2179_;
v___y_2262_ = v_a_2180_;
goto v___jp_2259_;
}
v___jp_2185_:
{
lean_object* v___f_2195_; lean_object* v_binders_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___f_2195_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__2));
v_binders_2196_ = l_Lean_Syntax_getArgs(v___y_2190_);
lean_dec(v___y_2190_);
v___x_2197_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__5);
v___x_2198_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8);
v___x_2199_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_2197_, v___f_2184_, v___x_2198_, v___f_2195_, v___y_2191_, v___y_2188_, v___y_2189_, v___y_2187_, v___y_2186_, v_binders_2196_, v_entries_x3f_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_a_2201_ = lean_ctor_get(v___x_2199_, 1);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2199_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2200_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
v_a_2209_ = lean_ctor_get(v___x_2199_, 0);
v_a_2210_ = lean_ctor_get(v___x_2199_, 1);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2199_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_inc(v_a_2209_);
lean_dec(v___x_2199_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2209_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
v___jp_2218_:
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___y_2226_);
v___y_2186_ = v___y_2219_;
v___y_2187_ = v___y_2220_;
v___y_2188_ = v___y_2222_;
v___y_2189_ = v___y_2224_;
v___y_2190_ = v___y_2223_;
v___y_2191_ = v___y_2227_;
v_entries_x3f_2192_ = v___x_2228_;
v___y_2193_ = v___y_2225_;
v___y_2194_ = v___y_2221_;
goto v___jp_2185_;
}
v___jp_2230_:
{
lean_object* v___x_2236_; lean_object* v_elabName_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v___x_2236_ = lean_unsigned_to_nat(3u);
v_elabName_2237_ = l_Lean_Syntax_getArg(v_x_2178_, v___x_2236_);
v___x_2238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_elabName_2237_);
v___x_2239_ = l_Lean_Syntax_isOfKind(v_elabName_2237_, v___x_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; 
lean_dec(v_elabName_2237_);
lean_dec(v_vis_x3f_2233_);
lean_dec(v___y_2232_);
lean_dec(v_x_2178_);
v___x_2240_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2235_);
return v___x_2240_;
}
else
{
lean_object* v___x_2241_; lean_object* v_type_2242_; uint8_t v___x_2243_; 
v___x_2241_ = lean_unsigned_to_nat(4u);
v_type_2242_ = l_Lean_Syntax_getArg(v_x_2178_, v___x_2241_);
lean_inc(v_type_2242_);
v___x_2243_ = l_Lean_Syntax_isOfKind(v_type_2242_, v___x_2238_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; 
lean_dec(v_type_2242_);
lean_dec(v_elabName_2237_);
lean_dec(v_vis_x3f_2233_);
lean_dec(v___y_2232_);
lean_dec(v_x_2178_);
v___x_2244_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2235_);
return v___x_2244_;
}
else
{
lean_object* v___x_2245_; lean_object* v_tk_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v___x_2245_ = lean_unsigned_to_nat(2u);
v_tk_2246_ = l_Lean_Syntax_getArg(v_x_2178_, v___x_2245_);
v___x_2247_ = lean_unsigned_to_nat(5u);
v___x_2248_ = l_Lean_Syntax_getArg(v_x_2178_, v___x_2247_);
v___x_2249_ = lean_unsigned_to_nat(6u);
v___x_2250_ = l_Lean_Syntax_getArg(v_x_2178_, v___x_2249_);
lean_dec(v_x_2178_);
v___x_2251_ = l_Lean_Syntax_isNone(v___x_2250_);
if (v___x_2251_ == 0)
{
uint8_t v___x_2252_; 
lean_inc(v___x_2250_);
v___x_2252_ = l_Lean_Syntax_matchesNull(v___x_2250_, v___y_2231_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; 
lean_dec(v___x_2250_);
lean_dec(v___x_2248_);
lean_dec(v_tk_2246_);
lean_dec(v_type_2242_);
lean_dec(v_elabName_2237_);
lean_dec(v_vis_x3f_2233_);
lean_dec(v___y_2232_);
v___x_2253_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2235_);
return v___x_2253_;
}
else
{
lean_object* v_entries_x3f_2254_; 
v_entries_x3f_2254_ = l_Lean_Syntax_getArg(v___x_2250_, v___x_2229_);
lean_dec(v___x_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_2254_);
v___x_2256_ = l_Lean_Syntax_isOfKind(v_entries_x3f_2254_, v___x_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; 
lean_dec(v_entries_x3f_2254_);
lean_dec(v___x_2248_);
lean_dec(v_tk_2246_);
lean_dec(v_type_2242_);
lean_dec(v_elabName_2237_);
lean_dec(v_vis_x3f_2233_);
lean_dec(v___y_2232_);
v___x_2257_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2235_);
return v___x_2257_;
}
else
{
v___y_2219_ = v_type_2242_;
v___y_2220_ = v_elabName_2237_;
v___y_2221_ = v___y_2235_;
v___y_2222_ = v_vis_x3f_2233_;
v___y_2223_ = v___x_2248_;
v___y_2224_ = v_tk_2246_;
v___y_2225_ = v___y_2234_;
v___y_2226_ = v_entries_x3f_2254_;
v___y_2227_ = v___y_2232_;
goto v___jp_2218_;
}
}
else
{
v___y_2219_ = v_type_2242_;
v___y_2220_ = v_elabName_2237_;
v___y_2221_ = v___y_2235_;
v___y_2222_ = v_vis_x3f_2233_;
v___y_2223_ = v___x_2248_;
v___y_2224_ = v_tk_2246_;
v___y_2225_ = v___y_2234_;
v___y_2226_ = v_entries_x3f_2254_;
v___y_2227_ = v___y_2232_;
goto v___jp_2218_;
}
}
}
else
{
lean_object* v___x_2258_; 
lean_dec(v___x_2250_);
v___x_2258_ = lean_box(0);
v___y_2186_ = v_type_2242_;
v___y_2187_ = v_elabName_2237_;
v___y_2188_ = v_vis_x3f_2233_;
v___y_2189_ = v_tk_2246_;
v___y_2190_ = v___x_2248_;
v___y_2191_ = v___y_2232_;
v_entries_x3f_2192_ = v___x_2258_;
v___y_2193_ = v___y_2234_;
v___y_2194_ = v___y_2235_;
goto v___jp_2185_;
}
}
}
}
v___jp_2259_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; 
v___x_2263_ = lean_unsigned_to_nat(1u);
v___x_2264_ = l_Lean_Syntax_getArg(v_x_2178_, v___x_2263_);
v___x_2265_ = l_Lean_Syntax_isNone(v___x_2264_);
if (v___x_2265_ == 0)
{
uint8_t v___x_2266_; 
lean_inc(v___x_2264_);
v___x_2266_ = l_Lean_Syntax_matchesNull(v___x_2264_, v___x_2263_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; 
lean_dec(v___x_2264_);
lean_dec(v_doc_x3f_2260_);
lean_dec(v_x_2178_);
v___x_2267_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2262_);
return v___x_2267_;
}
else
{
lean_object* v_vis_x3f_2268_; lean_object* v___x_2269_; 
v_vis_x3f_2268_ = l_Lean_Syntax_getArg(v___x_2264_, v___x_2229_);
lean_dec(v___x_2264_);
v___x_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2269_, 0, v_vis_x3f_2268_);
v___y_2231_ = v___x_2263_;
v___y_2232_ = v_doc_x3f_2260_;
v_vis_x3f_2233_ = v___x_2269_;
v___y_2234_ = v___y_2261_;
v___y_2235_ = v___y_2262_;
goto v___jp_2230_;
}
}
else
{
lean_object* v___x_2270_; 
lean_dec(v___x_2264_);
v___x_2270_ = lean_box(0);
v___y_2231_ = v___x_2263_;
v___y_2232_ = v_doc_x3f_2260_;
v_vis_x3f_2233_ = v___x_2270_;
v___y_2234_ = v___y_2261_;
v___y_2235_ = v___y_2262_;
goto v___jp_2230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___boxed(lean_object* v_x_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab(v_x_2283_, v_a_2284_, v_a_2285_);
lean_dec_ref(v_a_2284_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1(){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2294_ = l_Lean_Elab_macroAttribute;
v___x_2295_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__1));
v___x_2296_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1));
v___x_2297_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___boxed), 3, 0);
v___x_2298_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2294_, v___x_2295_, v___x_2296_, v___x_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___boxed(lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1();
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab(lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_2306_ = lean_unsigned_to_nat(2u);
v___x_2307_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_2305_, v___x_2306_, v_a_2301_, v_a_2302_, v_a_2303_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___boxed(lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab(v_a_2308_, v_a_2309_, v_a_2310_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
return v_res_2312_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___boxed), 4, 0);
v___x_2314_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_2314_, 0, v___x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1(){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTermConfigElab___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTermConfigElab__1___closed__1));
v___x_2317_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___closed__0);
v___x_2318_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_2316_, v___x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1___boxed(lean_object* v_a_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTermConfigElab__1();
return v_res_2320_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__0));
v___x_2323_ = l_String_toRawSubstring_x27(v___x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1(lean_object* v___x_2326_, lean_object* v___x_2327_, lean_object* v___x_2328_, lean_object* v___x_2329_, lean_object* v___x_2330_, lean_object* v_logExceptions_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_quotContext_2334_; lean_object* v_currMacroScope_2335_; lean_object* v_ref_2336_; uint8_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v_quotContext_2334_ = lean_ctor_get(v___y_2332_, 1);
v_currMacroScope_2335_ = lean_ctor_get(v___y_2332_, 2);
v_ref_2336_ = lean_ctor_get(v___y_2332_, 5);
v___x_2337_ = 0;
v___x_2338_ = l_Lean_SourceInfo_fromRef(v_ref_2336_, v___x_2337_);
v___x_2339_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__1));
v___x_2340_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__2));
lean_inc_n(v___x_2338_, 14);
v___x_2341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2338_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
v___x_2342_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__3));
lean_inc_ref_n(v___x_2328_, 5);
lean_inc_ref_n(v___x_2327_, 4);
lean_inc_ref_n(v___x_2326_, 9);
v___x_2343_ = l_Lean_Name_mkStr4(v___x_2326_, v___x_2327_, v___x_2328_, v___x_2342_);
v___x_2344_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__4));
v___x_2345_ = l_Lean_Name_mkStr4(v___x_2326_, v___x_2327_, v___x_2328_, v___x_2344_);
v___x_2346_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__5));
v___x_2347_ = l_Lean_Name_mkStr4(v___x_2326_, v___x_2327_, v___x_2328_, v___x_2346_);
v___x_2348_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__97));
v___x_2349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2338_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__7));
v___x_2351_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__9);
v___x_2352_ = lean_box(0);
lean_inc_n(v_currMacroScope_2335_, 3);
lean_inc_n(v_quotContext_2334_, 3);
v___x_2353_ = l_Lean_addMacroScope(v_quotContext_2334_, v___x_2352_, v_currMacroScope_2335_);
lean_inc_ref_n(v___x_2329_, 2);
v___x_2354_ = l_Lean_Name_mkStr3(v___x_2326_, v___x_2329_, v___x_2330_);
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
v___x_2356_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__10));
v___x_2357_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__2));
v___x_2358_ = l_Lean_Name_mkStr3(v___x_2326_, v___x_2356_, v___x_2357_);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
v___x_2360_ = l_Lean_Name_mkStr3(v___x_2326_, v___x_2329_, v___x_2357_);
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
v___x_2362_ = l_Lean_Name_mkStr3(v___x_2326_, v___x_2329_, v___x_2328_);
v___x_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
v___x_2364_ = l_Lean_Name_mkStr2(v___x_2326_, v___x_2356_);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
v___x_2366_ = lean_box(0);
v___x_2367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2363_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2361_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2359_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2355_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2338_);
lean_ctor_set(v___x_2372_, 1, v___x_2351_);
lean_ctor_set(v___x_2372_, 2, v___x_2353_);
lean_ctor_set(v___x_2372_, 3, v___x_2371_);
v___x_2373_ = l_Lean_Syntax_node1(v___x_2338_, v___x_2350_, v___x_2372_);
v___x_2374_ = l_Lean_Syntax_node2(v___x_2338_, v___x_2347_, v___x_2349_, v___x_2373_);
v___x_2375_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__11));
v___x_2376_ = l_Lean_Name_mkStr4(v___x_2326_, v___x_2327_, v___x_2328_, v___x_2375_);
v___x_2377_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__12));
v___x_2378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2338_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__66));
v___x_2380_ = l_Lean_Name_mkStr4(v___x_2326_, v___x_2327_, v___x_2328_, v___x_2379_);
v___x_2381_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__14);
v___x_2382_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__15));
v___x_2383_ = l_Lean_addMacroScope(v_quotContext_2334_, v___x_2382_, v_currMacroScope_2335_);
v___x_2384_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__19));
v___x_2385_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2338_);
lean_ctor_set(v___x_2385_, 1, v___x_2381_);
lean_ctor_set(v___x_2385_, 2, v___x_2383_);
lean_ctor_set(v___x_2385_, 3, v___x_2384_);
v___x_2386_ = l_Lean_Syntax_node1(v___x_2338_, v___x_2380_, v___x_2385_);
v___x_2387_ = l_Lean_Syntax_node2(v___x_2338_, v___x_2376_, v___x_2378_, v___x_2386_);
v___x_2388_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__102));
v___x_2389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2338_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = l_Lean_Syntax_node3(v___x_2338_, v___x_2345_, v___x_2374_, v___x_2387_, v___x_2389_);
v___x_2391_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___lam__1___closed__20));
v___x_2392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2338_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1, &l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__1);
v___x_2394_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___closed__2));
v___x_2395_ = l_Lean_addMacroScope(v_quotContext_2334_, v___x_2394_, v_currMacroScope_2335_);
v___x_2396_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2338_);
lean_ctor_set(v___x_2396_, 1, v___x_2393_);
lean_ctor_set(v___x_2396_, 2, v___x_2395_);
lean_ctor_set(v___x_2396_, 3, v___x_2366_);
v___x_2397_ = l_Lean_Syntax_node3(v___x_2338_, v___x_2343_, v___x_2390_, v___x_2392_, v___x_2396_);
v___x_2398_ = l_Lean_Syntax_node3(v___x_2338_, v___x_2339_, v_logExceptions_2331_, v___x_2341_, v___x_2397_);
v___x_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
lean_ctor_set(v___x_2399_, 1, v___y_2333_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1___boxed(lean_object* v___x_2400_, lean_object* v___x_2401_, lean_object* v___x_2402_, lean_object* v___x_2403_, lean_object* v___x_2404_, lean_object* v_logExceptions_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___lam__1(v___x_2400_, v___x_2401_, v___x_2402_, v___x_2403_, v___x_2404_, v_logExceptions_2405_, v___y_2406_, v___y_2407_);
lean_dec_ref(v___y_2406_);
return v_res_2408_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6(void){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__5));
v___x_2429_ = l_Lean_mkCIdent(v___x_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig(lean_object* v_x_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2433_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1));
lean_inc(v_x_2430_);
v___x_2434_ = l_Lean_Syntax_isOfKind(v_x_2430_, v___x_2433_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; 
lean_dec(v_x_2430_);
v___x_2435_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2432_);
return v___x_2435_;
}
else
{
lean_object* v___f_2436_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v_entries_x3f_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___x_2481_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v_vis_x3f_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v_doc_x3f_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___f_2436_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__3));
v___x_2481_ = lean_unsigned_to_nat(0u);
v___x_2523_ = l_Lean_Syntax_getArg(v_x_2430_, v___x_2481_);
v___x_2524_ = l_Lean_Syntax_isNone(v___x_2523_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; uint8_t v___x_2526_; 
v___x_2525_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2523_);
v___x_2526_ = l_Lean_Syntax_matchesNull(v___x_2523_, v___x_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; 
lean_dec(v___x_2523_);
lean_dec(v_x_2430_);
v___x_2527_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2432_);
return v___x_2527_;
}
else
{
lean_object* v_doc_x3f_2528_; 
v_doc_x3f_2528_ = l_Lean_Syntax_getArg(v___x_2523_, v___x_2481_);
lean_dec(v___x_2523_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2531_; uint8_t v___x_2532_; 
v___x_2531_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_2528_);
v___x_2532_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2528_, v___x_2531_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; 
lean_dec(v_doc_x3f_2528_);
lean_dec(v_x_2430_);
v___x_2533_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2432_);
return v___x_2533_;
}
else
{
goto v___jp_2529_;
}
}
else
{
goto v___jp_2529_;
}
v___jp_2529_:
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2530_, 0, v_doc_x3f_2528_);
v_doc_x3f_2512_ = v___x_2530_;
v___y_2513_ = v_a_2431_;
v___y_2514_ = v_a_2432_;
goto v___jp_2511_;
}
}
}
else
{
lean_object* v___x_2534_; 
lean_dec(v___x_2523_);
v___x_2534_ = lean_box(0);
v_doc_x3f_2512_ = v___x_2534_;
v___y_2513_ = v_a_2431_;
v___y_2514_ = v_a_2432_;
goto v___jp_2511_;
}
v___jp_2437_:
{
lean_object* v___f_2447_; lean_object* v_binders_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___f_2447_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__2));
v_binders_2448_ = l_Lean_Syntax_getArgs(v___y_2439_);
lean_dec(v___y_2439_);
v___x_2449_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6, &l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__6);
v___x_2450_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8);
v___x_2451_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_2449_, v___f_2436_, v___x_2450_, v___f_2447_, v___y_2438_, v___y_2442_, v___y_2441_, v___y_2443_, v___y_2440_, v_binders_2448_, v_entries_x3f_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_a_2453_ = lean_ctor_get(v___x_2451_, 1);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2451_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2452_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
else
{
lean_object* v_a_2461_; lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
v_a_2461_ = lean_ctor_get(v___x_2451_, 0);
v_a_2462_ = lean_ctor_get(v___x_2451_, 1);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2451_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_inc(v_a_2461_);
lean_dec(v___x_2451_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2461_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
v___jp_2470_:
{
lean_object* v___x_2480_; 
v___x_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___y_2474_);
v___y_2438_ = v___y_2471_;
v___y_2439_ = v___y_2472_;
v___y_2440_ = v___y_2473_;
v___y_2441_ = v___y_2475_;
v___y_2442_ = v___y_2477_;
v___y_2443_ = v___y_2479_;
v_entries_x3f_2444_ = v___x_2480_;
v___y_2445_ = v___y_2476_;
v___y_2446_ = v___y_2478_;
goto v___jp_2437_;
}
v___jp_2482_:
{
lean_object* v___x_2488_; lean_object* v_elabName_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
v___x_2488_ = lean_unsigned_to_nat(3u);
v_elabName_2489_ = l_Lean_Syntax_getArg(v_x_2430_, v___x_2488_);
v___x_2490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_elabName_2489_);
v___x_2491_ = l_Lean_Syntax_isOfKind(v_elabName_2489_, v___x_2490_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; 
lean_dec(v_elabName_2489_);
lean_dec(v_vis_x3f_2485_);
lean_dec(v___y_2483_);
lean_dec(v_x_2430_);
v___x_2492_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2487_);
return v___x_2492_;
}
else
{
lean_object* v___x_2493_; lean_object* v_type_2494_; uint8_t v___x_2495_; 
v___x_2493_ = lean_unsigned_to_nat(4u);
v_type_2494_ = l_Lean_Syntax_getArg(v_x_2430_, v___x_2493_);
lean_inc(v_type_2494_);
v___x_2495_ = l_Lean_Syntax_isOfKind(v_type_2494_, v___x_2490_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; 
lean_dec(v_type_2494_);
lean_dec(v_elabName_2489_);
lean_dec(v_vis_x3f_2485_);
lean_dec(v___y_2483_);
lean_dec(v_x_2430_);
v___x_2496_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2487_);
return v___x_2496_;
}
else
{
lean_object* v___x_2497_; lean_object* v_tk_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2497_ = lean_unsigned_to_nat(2u);
v_tk_2498_ = l_Lean_Syntax_getArg(v_x_2430_, v___x_2497_);
v___x_2499_ = lean_unsigned_to_nat(5u);
v___x_2500_ = l_Lean_Syntax_getArg(v_x_2430_, v___x_2499_);
v___x_2501_ = lean_unsigned_to_nat(6u);
v___x_2502_ = l_Lean_Syntax_getArg(v_x_2430_, v___x_2501_);
lean_dec(v_x_2430_);
v___x_2503_ = l_Lean_Syntax_isNone(v___x_2502_);
if (v___x_2503_ == 0)
{
uint8_t v___x_2504_; 
lean_inc(v___x_2502_);
v___x_2504_ = l_Lean_Syntax_matchesNull(v___x_2502_, v___y_2484_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; 
lean_dec(v___x_2502_);
lean_dec(v___x_2500_);
lean_dec(v_tk_2498_);
lean_dec(v_type_2494_);
lean_dec(v_elabName_2489_);
lean_dec(v_vis_x3f_2485_);
lean_dec(v___y_2483_);
v___x_2505_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2487_);
return v___x_2505_;
}
else
{
lean_object* v_entries_x3f_2506_; 
v_entries_x3f_2506_ = l_Lean_Syntax_getArg(v___x_2502_, v___x_2481_);
lean_dec(v___x_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2507_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_2506_);
v___x_2508_ = l_Lean_Syntax_isOfKind(v_entries_x3f_2506_, v___x_2507_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; 
lean_dec(v_entries_x3f_2506_);
lean_dec(v___x_2500_);
lean_dec(v_tk_2498_);
lean_dec(v_type_2494_);
lean_dec(v_elabName_2489_);
lean_dec(v_vis_x3f_2485_);
lean_dec(v___y_2483_);
v___x_2509_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2487_);
return v___x_2509_;
}
else
{
v___y_2471_ = v___y_2483_;
v___y_2472_ = v___x_2500_;
v___y_2473_ = v_type_2494_;
v___y_2474_ = v_entries_x3f_2506_;
v___y_2475_ = v_tk_2498_;
v___y_2476_ = v___y_2486_;
v___y_2477_ = v_vis_x3f_2485_;
v___y_2478_ = v___y_2487_;
v___y_2479_ = v_elabName_2489_;
goto v___jp_2470_;
}
}
else
{
v___y_2471_ = v___y_2483_;
v___y_2472_ = v___x_2500_;
v___y_2473_ = v_type_2494_;
v___y_2474_ = v_entries_x3f_2506_;
v___y_2475_ = v_tk_2498_;
v___y_2476_ = v___y_2486_;
v___y_2477_ = v_vis_x3f_2485_;
v___y_2478_ = v___y_2487_;
v___y_2479_ = v_elabName_2489_;
goto v___jp_2470_;
}
}
}
else
{
lean_object* v___x_2510_; 
lean_dec(v___x_2502_);
v___x_2510_ = lean_box(0);
v___y_2438_ = v___y_2483_;
v___y_2439_ = v___x_2500_;
v___y_2440_ = v_type_2494_;
v___y_2441_ = v_tk_2498_;
v___y_2442_ = v_vis_x3f_2485_;
v___y_2443_ = v_elabName_2489_;
v_entries_x3f_2444_ = v___x_2510_;
v___y_2445_ = v___y_2486_;
v___y_2446_ = v___y_2487_;
goto v___jp_2437_;
}
}
}
}
v___jp_2511_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v___x_2515_ = lean_unsigned_to_nat(1u);
v___x_2516_ = l_Lean_Syntax_getArg(v_x_2430_, v___x_2515_);
v___x_2517_ = l_Lean_Syntax_isNone(v___x_2516_);
if (v___x_2517_ == 0)
{
uint8_t v___x_2518_; 
lean_inc(v___x_2516_);
v___x_2518_ = l_Lean_Syntax_matchesNull(v___x_2516_, v___x_2515_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; 
lean_dec(v___x_2516_);
lean_dec(v_doc_x3f_2512_);
lean_dec(v_x_2430_);
v___x_2519_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2514_);
return v___x_2519_;
}
else
{
lean_object* v_vis_x3f_2520_; lean_object* v___x_2521_; 
v_vis_x3f_2520_ = l_Lean_Syntax_getArg(v___x_2516_, v___x_2481_);
lean_dec(v___x_2516_);
v___x_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2521_, 0, v_vis_x3f_2520_);
v___y_2483_ = v_doc_x3f_2512_;
v___y_2484_ = v___x_2515_;
v_vis_x3f_2485_ = v___x_2521_;
v___y_2486_ = v___y_2513_;
v___y_2487_ = v___y_2514_;
goto v___jp_2482_;
}
}
else
{
lean_object* v___x_2522_; 
lean_dec(v___x_2516_);
v___x_2522_ = lean_box(0);
v___y_2483_ = v_doc_x3f_2512_;
v___y_2484_ = v___x_2515_;
v_vis_x3f_2485_ = v___x_2522_;
v___y_2486_ = v___y_2513_;
v___y_2487_ = v___y_2514_;
goto v___jp_2482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___boxed(lean_object* v_x_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Elab_ConfigEval_elabDeclareTacticConfig(v_x_2535_, v_a_2536_, v_a_2537_);
lean_dec_ref(v_a_2536_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1(){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2546_ = l_Lean_Elab_macroAttribute;
v___x_2547_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___closed__1));
v___x_2548_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1));
v___x_2549_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeclareTacticConfig___boxed), 3, 0);
v___x_2550_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2546_, v___x_2547_, v___x_2548_, v___x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___boxed(lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1();
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig(lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_2558_ = lean_unsigned_to_nat(2u);
v___x_2559_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_2557_, v___x_2558_, v_a_2553_, v_a_2554_, v_a_2555_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___boxed(lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig(v_a_2560_, v_a_2561_, v_a_2562_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
return v_res_2564_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___boxed), 4, 0);
v___x_2566_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_2566_, 0, v___x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1(){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2568_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareTacticConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareTacticConfig__1___closed__1));
v___x_2569_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___closed__0);
v___x_2570_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_2568_, v___x_2569_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1___boxed(lean_object* v_a_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDeclareTacticConfig__1();
return v_res_2572_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__0));
v___x_2575_ = l_String_toRawSubstring_x27(v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1(lean_object* v___x_2577_, lean_object* v___x_2578_, lean_object* v___x_2579_, lean_object* v___x_2580_, lean_object* v___x_2581_, lean_object* v_eval_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_quotContext_2585_; lean_object* v_currMacroScope_2586_; lean_object* v_ref_2587_; uint8_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v_quotContext_2585_ = lean_ctor_get(v___y_2583_, 1);
v_currMacroScope_2586_ = lean_ctor_get(v___y_2583_, 2);
v_ref_2587_ = lean_ctor_get(v___y_2583_, 5);
v___x_2588_ = 0;
v___x_2589_ = l_Lean_SourceInfo_fromRef(v_ref_2587_, v___x_2588_);
v___x_2590_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd___closed__82));
lean_inc_ref(v___x_2577_);
v___x_2591_ = l_Lean_Name_mkStr4(v___x_2577_, v___x_2578_, v___x_2579_, v___x_2590_);
v___x_2592_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1, &l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1_once, _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__1);
v___x_2593_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___closed__2));
lean_inc_ref(v___x_2580_);
v___x_2594_ = l_Lean_Name_mkStr2(v___x_2580_, v___x_2593_);
lean_inc(v_currMacroScope_2586_);
lean_inc(v_quotContext_2585_);
v___x_2595_ = l_Lean_addMacroScope(v_quotContext_2585_, v___x_2594_, v_currMacroScope_2586_);
v___x_2596_ = l_Lean_Name_mkStr4(v___x_2577_, v___x_2581_, v___x_2580_, v___x_2593_);
v___x_2597_ = lean_box(0);
lean_inc(v___x_2596_);
v___x_2598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2596_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2596_);
v___x_2600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v___x_2597_);
v___x_2601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2598_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
lean_inc_n(v___x_2589_, 2);
v___x_2602_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2589_);
lean_ctor_set(v___x_2602_, 1, v___x_2592_);
lean_ctor_set(v___x_2602_, 2, v___x_2595_);
lean_ctor_set(v___x_2602_, 3, v___x_2601_);
v___x_2603_ = ((lean_object*)(l_Lean_Elab_ConfigEval_expandEnsureEvalTermExprInstance___closed__5));
v___x_2604_ = l_Lean_Syntax_node1(v___x_2589_, v___x_2603_, v_eval_2582_);
v___x_2605_ = l_Lean_Syntax_node2(v___x_2589_, v___x_2591_, v___x_2602_, v___x_2604_);
v___x_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
lean_ctor_set(v___x_2606_, 1, v___y_2584_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1___boxed(lean_object* v___x_2607_, lean_object* v___x_2608_, lean_object* v___x_2609_, lean_object* v___x_2610_, lean_object* v___x_2611_, lean_object* v_eval_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___lam__1(v___x_2607_, v___x_2608_, v___x_2609_, v___x_2610_, v___x_2611_, v_eval_2612_, v___y_2613_, v___y_2614_);
lean_dec_ref(v___y_2613_);
return v_res_2615_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__4));
v___x_2635_ = l_Lean_mkCIdent(v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig(lean_object* v_x_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_){
_start:
{
lean_object* v___x_2639_; uint8_t v___x_2640_; 
v___x_2639_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1));
lean_inc(v_x_2636_);
v___x_2640_ = l_Lean_Syntax_isOfKind(v_x_2636_, v___x_2639_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; 
lean_dec(v_x_2636_);
v___x_2641_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2638_);
return v___x_2641_;
}
else
{
lean_object* v___f_2642_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v_entries_x3f_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___x_2687_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v_vis_x3f_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v_doc_x3f_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___f_2642_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCoreConfigElab___closed__2));
v___x_2687_ = lean_unsigned_to_nat(0u);
v___x_2729_ = l_Lean_Syntax_getArg(v_x_2636_, v___x_2687_);
v___x_2730_ = l_Lean_Syntax_isNone(v___x_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2731_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2729_);
v___x_2732_ = l_Lean_Syntax_matchesNull(v___x_2729_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; 
lean_dec(v___x_2729_);
lean_dec(v_x_2636_);
v___x_2733_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2638_);
return v___x_2733_;
}
else
{
lean_object* v_doc_x3f_2734_; 
v_doc_x3f_2734_ = l_Lean_Syntax_getArg(v___x_2729_, v___x_2687_);
lean_dec(v___x_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2737_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDefEvalConfigItemCmd___closed__4));
lean_inc(v_doc_x3f_2734_);
v___x_2738_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2734_, v___x_2737_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; 
lean_dec(v_doc_x3f_2734_);
lean_dec(v_x_2636_);
v___x_2739_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2638_);
return v___x_2739_;
}
else
{
goto v___jp_2735_;
}
}
else
{
goto v___jp_2735_;
}
v___jp_2735_:
{
lean_object* v___x_2736_; 
v___x_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2736_, 0, v_doc_x3f_2734_);
v_doc_x3f_2718_ = v___x_2736_;
v___y_2719_ = v_a_2637_;
v___y_2720_ = v_a_2638_;
goto v___jp_2717_;
}
}
}
else
{
lean_object* v___x_2740_; 
lean_dec(v___x_2729_);
v___x_2740_ = lean_box(0);
v_doc_x3f_2718_ = v___x_2740_;
v___y_2719_ = v_a_2637_;
v___y_2720_ = v_a_2638_;
goto v___jp_2717_;
}
v___jp_2643_:
{
lean_object* v_binders_2653_; lean_object* v___f_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v_binders_2653_ = l_Lean_Syntax_getArgs(v___y_2649_);
lean_dec(v___y_2649_);
v___f_2654_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__2));
v___x_2655_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5, &l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5_once, _init_l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__5);
v___x_2656_ = lean_obj_once(&l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8, &l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8_once, _init_l_Lean_Elab_ConfigEval_elabDeclareTermConfigElab___closed__8);
v___x_2657_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_mkElabConfigCmd(v___x_2655_, v___f_2654_, v___x_2656_, v___f_2642_, v___y_2647_, v___y_2648_, v___y_2645_, v___y_2644_, v___y_2646_, v_binders_2653_, v_entries_x3f_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_a_2659_ = lean_ctor_get(v___x_2657_, 1);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2657_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2658_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
v_a_2667_ = lean_ctor_get(v___x_2657_, 0);
v_a_2668_ = lean_ctor_get(v___x_2657_, 1);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2657_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_inc(v_a_2667_);
lean_dec(v___x_2657_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2667_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
v___jp_2676_:
{
lean_object* v___x_2686_; 
v___x_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___y_2678_);
v___y_2644_ = v___y_2677_;
v___y_2645_ = v___y_2679_;
v___y_2646_ = v___y_2683_;
v___y_2647_ = v___y_2682_;
v___y_2648_ = v___y_2684_;
v___y_2649_ = v___y_2685_;
v_entries_x3f_2650_ = v___x_2686_;
v___y_2651_ = v___y_2681_;
v___y_2652_ = v___y_2680_;
goto v___jp_2643_;
}
v___jp_2688_:
{
lean_object* v___x_2694_; lean_object* v_elabName_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2694_ = lean_unsigned_to_nat(3u);
v_elabName_2695_ = l_Lean_Syntax_getArg(v_x_2636_, v___x_2694_);
v___x_2696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_mkEvalConfigItemView_spec__4___redArg___closed__13));
lean_inc(v_elabName_2695_);
v___x_2697_ = l_Lean_Syntax_isOfKind(v_elabName_2695_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; 
lean_dec(v_elabName_2695_);
lean_dec(v_vis_x3f_2691_);
lean_dec(v___y_2689_);
lean_dec(v_x_2636_);
v___x_2698_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2693_);
return v___x_2698_;
}
else
{
lean_object* v___x_2699_; lean_object* v_type_2700_; uint8_t v___x_2701_; 
v___x_2699_ = lean_unsigned_to_nat(4u);
v_type_2700_ = l_Lean_Syntax_getArg(v_x_2636_, v___x_2699_);
lean_inc(v_type_2700_);
v___x_2701_ = l_Lean_Syntax_isOfKind(v_type_2700_, v___x_2696_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; 
lean_dec(v_type_2700_);
lean_dec(v_elabName_2695_);
lean_dec(v_vis_x3f_2691_);
lean_dec(v___y_2689_);
lean_dec(v_x_2636_);
v___x_2702_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2693_);
return v___x_2702_;
}
else
{
lean_object* v___x_2703_; lean_object* v_tk_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2703_ = lean_unsigned_to_nat(2u);
v_tk_2704_ = l_Lean_Syntax_getArg(v_x_2636_, v___x_2703_);
v___x_2705_ = lean_unsigned_to_nat(5u);
v___x_2706_ = l_Lean_Syntax_getArg(v_x_2636_, v___x_2705_);
v___x_2707_ = lean_unsigned_to_nat(6u);
v___x_2708_ = l_Lean_Syntax_getArg(v_x_2636_, v___x_2707_);
lean_dec(v_x_2636_);
v___x_2709_ = l_Lean_Syntax_isNone(v___x_2708_);
if (v___x_2709_ == 0)
{
uint8_t v___x_2710_; 
lean_inc(v___x_2708_);
v___x_2710_ = l_Lean_Syntax_matchesNull(v___x_2708_, v___y_2690_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; 
lean_dec(v___x_2708_);
lean_dec(v___x_2706_);
lean_dec(v_tk_2704_);
lean_dec(v_type_2700_);
lean_dec(v_elabName_2695_);
lean_dec(v_vis_x3f_2691_);
lean_dec(v___y_2689_);
v___x_2711_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2693_);
return v___x_2711_;
}
else
{
lean_object* v_entries_x3f_2712_; 
v_entries_x3f_2712_ = l_Lean_Syntax_getArg(v___x_2708_, v___x_2687_);
lean_dec(v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2713_ = ((lean_object*)(l_Lean_Elab_ConfigEval_mkEvalConfigItemView___closed__3));
lean_inc(v_entries_x3f_2712_);
v___x_2714_ = l_Lean_Syntax_isOfKind(v_entries_x3f_2712_, v___x_2713_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; 
lean_dec(v_entries_x3f_2712_);
lean_dec(v___x_2706_);
lean_dec(v_tk_2704_);
lean_dec(v_type_2700_);
lean_dec(v_elabName_2695_);
lean_dec(v_vis_x3f_2691_);
lean_dec(v___y_2689_);
v___x_2715_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2693_);
return v___x_2715_;
}
else
{
v___y_2677_ = v_elabName_2695_;
v___y_2678_ = v_entries_x3f_2712_;
v___y_2679_ = v_tk_2704_;
v___y_2680_ = v___y_2693_;
v___y_2681_ = v___y_2692_;
v___y_2682_ = v___y_2689_;
v___y_2683_ = v_type_2700_;
v___y_2684_ = v_vis_x3f_2691_;
v___y_2685_ = v___x_2706_;
goto v___jp_2676_;
}
}
else
{
v___y_2677_ = v_elabName_2695_;
v___y_2678_ = v_entries_x3f_2712_;
v___y_2679_ = v_tk_2704_;
v___y_2680_ = v___y_2693_;
v___y_2681_ = v___y_2692_;
v___y_2682_ = v___y_2689_;
v___y_2683_ = v_type_2700_;
v___y_2684_ = v_vis_x3f_2691_;
v___y_2685_ = v___x_2706_;
goto v___jp_2676_;
}
}
}
else
{
lean_object* v___x_2716_; 
lean_dec(v___x_2708_);
v___x_2716_ = lean_box(0);
v___y_2644_ = v_elabName_2695_;
v___y_2645_ = v_tk_2704_;
v___y_2646_ = v_type_2700_;
v___y_2647_ = v___y_2689_;
v___y_2648_ = v_vis_x3f_2691_;
v___y_2649_ = v___x_2706_;
v_entries_x3f_2650_ = v___x_2716_;
v___y_2651_ = v___y_2692_;
v___y_2652_ = v___y_2693_;
goto v___jp_2643_;
}
}
}
}
v___jp_2717_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; uint8_t v___x_2723_; 
v___x_2721_ = lean_unsigned_to_nat(1u);
v___x_2722_ = l_Lean_Syntax_getArg(v_x_2636_, v___x_2721_);
v___x_2723_ = l_Lean_Syntax_isNone(v___x_2722_);
if (v___x_2723_ == 0)
{
uint8_t v___x_2724_; 
lean_inc(v___x_2722_);
v___x_2724_ = l_Lean_Syntax_matchesNull(v___x_2722_, v___x_2721_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; 
lean_dec(v___x_2722_);
lean_dec(v_doc_x3f_2718_);
lean_dec(v_x_2636_);
v___x_2725_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2720_);
return v___x_2725_;
}
else
{
lean_object* v_vis_x3f_2726_; lean_object* v___x_2727_; 
v_vis_x3f_2726_ = l_Lean_Syntax_getArg(v___x_2722_, v___x_2687_);
lean_dec(v___x_2722_);
v___x_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2727_, 0, v_vis_x3f_2726_);
v___y_2689_ = v_doc_x3f_2718_;
v___y_2690_ = v___x_2721_;
v_vis_x3f_2691_ = v___x_2727_;
v___y_2692_ = v___y_2719_;
v___y_2693_ = v___y_2720_;
goto v___jp_2688_;
}
}
else
{
lean_object* v___x_2728_; 
lean_dec(v___x_2722_);
v___x_2728_ = lean_box(0);
v___y_2689_ = v_doc_x3f_2718_;
v___y_2690_ = v___x_2721_;
v_vis_x3f_2691_ = v___x_2728_;
v___y_2692_ = v___y_2719_;
v___y_2693_ = v___y_2720_;
goto v___jp_2688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___boxed(lean_object* v_x_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_Elab_ConfigEval_elabDeclareCommandConfig(v_x_2741_, v_a_2742_, v_a_2743_);
lean_dec_ref(v_a_2742_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1(){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2752_ = l_Lean_Elab_macroAttribute;
v___x_2753_ = ((lean_object*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___closed__1));
v___x_2754_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1));
v___x_2755_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_elabDeclareCommandConfig___boxed), 3, 0);
v___x_2756_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2752_, v___x_2753_, v___x_2754_, v___x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___boxed(lean_object* v_a_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1();
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab(lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2763_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkDefEvalConfigItemCmd___closed__0));
v___x_2764_ = lean_unsigned_to_nat(2u);
v___x_2765_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_2763_, v___x_2764_, v_a_2759_, v_a_2760_, v_a_2761_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___boxed(lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab(v_a_2766_, v_a_2767_, v_a_2768_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
return v_res_2770_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___boxed), 4, 0);
v___x_2772_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_2772_, 0, v___x_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1(){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2774_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_elabDeclareCommandConfig___regBuiltin_Lean_Elab_ConfigEval_elabDeclareCommandConfig__1___closed__1));
v___x_2775_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0, &l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___closed__0);
v___x_2776_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_2774_, v___x_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1___boxed(lean_object* v_a_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab___regBuiltin___private_Lean_Elab_ConfigEval_Builtins_0__Lean_Elab_ConfigEval_checkCommandConfigElab__1();
return v_res_2778_;
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
