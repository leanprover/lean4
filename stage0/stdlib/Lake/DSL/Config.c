// Lean compiler output
// Module: Lake.DSL.Config
// Imports: public import Lean.Elab.Term import Lake.DSL.Extensions import Lake.DSL.Syntax import Lake.Util.Name
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lake_optsExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_dirExt;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkCApp(lean_object*, lean_object*);
extern lean_object* l_Lake_nameExt;
extern lean_object* l_Lake_DSL_packageDeclName;
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lake_Name_quoteFrom(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__1 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__2 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__2_value),LEAN_SCALAR_PTR_LITERAL(35, 98, 18, 79, 25, 208, 83, 100)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "origName"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5_value;
static lean_once_cell_t l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6;
static lean_once_cell_t l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "`__name__` can only be used after the `package` declaration"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8_value;
static lean_once_cell_t l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "nameConst"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(97, 173, 245, 76, 54, 29, 98, 170)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__5_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__6 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__6_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__7_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Config"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__8 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__8_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__7_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(51, 163, 92, 14, 113, 68, 142, 199)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__9 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(158, 136, 179, 87, 206, 219, 188, 185)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__10 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__10_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__10_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 37, 193, 91, 34, 28, 65, 43)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__11 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__11_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__11_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 244, 218, 94, 186, 54, 214, 243)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabNameConst"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__13 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__13_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(114, 1, 213, 9, 23, 223, 204, 252)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___boxed(lean_object*);
static const lean_string_object l_Lake_DSL_dummyDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_DSL_dummyDir___closed__0 = (const lean_object*)&l_Lake_DSL_dummyDir___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_DSL_dummyDir = (const lean_object*)&l_Lake_DSL_dummyDir___closed__0_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "System"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__0 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__0_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "FilePath"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__1 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__2 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(249, 26, 71, 103, 26, 96, 3, 234)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 100, 64, 177, 244, 49, 208, 176)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__4 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dummyDir"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__6 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__6_value),LEAN_SCALAR_PTR_LITERAL(168, 30, 196, 202, 165, 130, 85, 171)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dirConst"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 238, 150, 168, 55, 12, 135, 204)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabDirConst"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 234, 240, 117, 33, 82, 87, 34)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f___redArg();
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "getConfig"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__0 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 0, 210, 145, 234, 91, 2, 92)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__4 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value_aux_2),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6_value;
static lean_once_cell_t l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6_value),LEAN_SCALAR_PTR_LITERAL(37, 202, 7, 33, 103, 74, 114, 212)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__11 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__11_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__13 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__13_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__15 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__15_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value_aux_2),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__15_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__17 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__17_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value_aux_2),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__17_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__20 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__20_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__20_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21_value;
static lean_once_cell_t l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__23_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__24 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__24_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__26_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__27 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__27_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__25_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__28_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__29 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__29_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__30 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__30_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__30_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__31 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__31_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__32 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__32_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__29_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__32_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__33 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__33_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__27_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__33_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__34 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__34_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__24_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__34_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36_value;
static lean_once_cell_t l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36_value),LEAN_SCALAR_PTR_LITERAL(73, 239, 30, 105, 8, 60, 178, 241)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__40 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__40_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__40_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42_value;
static lean_once_cell_t l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__45 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__45_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__46 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__46_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__47_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__48 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__48_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__49 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__49_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__46_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__49_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__50 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__50_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__45_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__50_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52_value;
static lean_once_cell_t l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__55 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__55_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__56 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__56_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52_value),LEAN_SCALAR_PTR_LITERAL(143, 111, 143, 134, 134, 69, 118, 12)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__56_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__55_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dummyGetConfig\?"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value),LEAN_SCALAR_PTR_LITERAL(43, 158, 45, 71, 114, 122, 16, 88)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__66_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__66_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__66_value_aux_2),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__66 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__66_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__67 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__67_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__68 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__68_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabGetConfig"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__12_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 181, 23, 57, 213, 234, 225, 20)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___boxed(lean_object*);
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_box(1);
v___x_2_ = l_Lean_MessageData_ofFormat(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__2));
v___x_7_ = l_Lean_MessageData_ofFormat(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7(lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
return v_x_8_;
}
else
{
lean_object* v_head_10_; lean_object* v_tail_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_33_; 
v_head_10_ = lean_ctor_get(v_x_9_, 0);
v_tail_11_ = lean_ctor_get(v_x_9_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_x_9_);
if (v_isSharedCheck_33_ == 0)
{
v___x_13_ = v_x_9_;
v_isShared_14_ = v_isSharedCheck_33_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_tail_11_);
lean_inc(v_head_10_);
lean_dec(v_x_9_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_33_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v_before_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_31_; 
v_before_15_ = lean_ctor_get(v_head_10_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v_head_10_);
if (v_isSharedCheck_31_ == 0)
{
lean_object* v_unused_32_; 
v_unused_32_ = lean_ctor_get(v_head_10_, 1);
lean_dec(v_unused_32_);
v___x_17_ = v_head_10_;
v_isShared_18_ = v_isSharedCheck_31_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_before_15_);
lean_dec(v_head_10_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_31_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_19_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__0);
if (v_isShared_18_ == 0)
{
lean_ctor_set_tag(v___x_17_, 7);
lean_ctor_set(v___x_17_, 1, v___x_19_);
lean_ctor_set(v___x_17_, 0, v_x_8_);
v___x_21_ = v___x_17_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_x_8_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v___x_19_);
v___x_21_ = v_reuseFailAlloc_30_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_22_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__3);
if (v_isShared_14_ == 0)
{
lean_ctor_set_tag(v___x_13_, 7);
lean_ctor_set(v___x_13_, 1, v___x_22_);
lean_ctor_set(v___x_13_, 0, v___x_21_);
v___x_24_ = v___x_13_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_21_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v___x_22_);
v___x_24_ = v_reuseFailAlloc_29_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = l_Lean_MessageData_ofSyntax(v_before_15_);
v___x_26_ = l_Lean_indentD(v___x_25_);
v___x_27_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_24_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
v_x_8_ = v___x_27_;
v_x_9_ = v_tail_11_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__6(lean_object* v_opts_34_, lean_object* v_opt_35_){
_start:
{
lean_object* v_name_36_; lean_object* v_defValue_37_; lean_object* v_map_38_; lean_object* v___x_39_; 
v_name_36_ = lean_ctor_get(v_opt_35_, 0);
v_defValue_37_ = lean_ctor_get(v_opt_35_, 1);
v_map_38_ = lean_ctor_get(v_opts_34_, 0);
v___x_39_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_38_, v_name_36_);
if (lean_obj_tag(v___x_39_) == 0)
{
uint8_t v___x_40_; 
v___x_40_ = lean_unbox(v_defValue_37_);
return v___x_40_;
}
else
{
lean_object* v_val_41_; 
v_val_41_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_val_41_);
lean_dec_ref_known(v___x_39_, 1);
if (lean_obj_tag(v_val_41_) == 1)
{
uint8_t v_v_42_; 
v_v_42_ = lean_ctor_get_uint8(v_val_41_, 0);
lean_dec_ref_known(v_val_41_, 0);
return v_v_42_;
}
else
{
uint8_t v___x_43_; 
lean_dec(v_val_41_);
v___x_43_ = lean_unbox(v_defValue_37_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__6___boxed(lean_object* v_opts_44_, lean_object* v_opt_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__6(v_opts_44_, v_opt_45_);
lean_dec_ref(v_opt_45_);
lean_dec_ref(v_opts_44_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__1));
v___x_52_ = l_Lean_MessageData_ofFormat(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg(lean_object* v_msgData_53_, lean_object* v_macroStack_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_57_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_55_);
v___x_58_ = l_Lean_Elab_pp_macroStack;
v___x_59_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__6(v___x_57_, v___x_58_);
lean_dec_ref(v___x_57_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
lean_dec(v_macroStack_54_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v_msgData_53_);
return v___x_60_;
}
else
{
if (lean_obj_tag(v_macroStack_54_) == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_msgData_53_);
return v___x_61_;
}
else
{
lean_object* v_head_62_; lean_object* v_after_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_78_; 
v_head_62_ = lean_ctor_get(v_macroStack_54_, 0);
lean_inc(v_head_62_);
v_after_63_ = lean_ctor_get(v_head_62_, 1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_head_62_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; 
v_unused_79_ = lean_ctor_get(v_head_62_, 0);
lean_dec(v_unused_79_);
v___x_65_ = v_head_62_;
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_after_63_);
lean_dec(v_head_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7___closed__0);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 7);
lean_ctor_set(v___x_65_, 1, v___x_67_);
lean_ctor_set(v___x_65_, 0, v_msgData_53_);
v___x_69_ = v___x_65_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_msgData_53_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v___x_67_);
v___x_69_ = v_reuseFailAlloc_77_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v_msgData_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_70_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___closed__2);
v___x_71_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = l_Lean_MessageData_ofSyntax(v_after_63_);
v___x_73_ = l_Lean_indentD(v___x_72_);
v_msgData_74_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_74_, 0, v___x_71_);
lean_ctor_set(v_msgData_74_, 1, v___x_73_);
v___x_75_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4_spec__7(v_msgData_74_, v_macroStack_54_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_80_, lean_object* v_macroStack_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg(v_msgData_80_, v_macroStack_81_, v___y_82_);
lean_dec_ref(v___y_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3(lean_object* v_msgData_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_env_92_; uint8_t v___x_93_; lean_object* v_env_94_; lean_object* v___x_95_; lean_object* v_toCold_96_; lean_object* v_mctx_97_; lean_object* v_lctx_98_; lean_object* v_options_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_91_ = lean_st_ref_get(v___y_89_);
v_env_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_env_92_);
lean_dec(v___x_91_);
v___x_93_ = 0;
v_env_94_ = l_Lean_Environment_setRecordingDeps(v_env_92_, v___x_93_);
v___x_95_ = lean_st_ref_get(v___y_87_);
v_toCold_96_ = lean_ctor_get(v___y_88_, 0);
v_mctx_97_ = lean_ctor_get(v___x_95_, 0);
lean_inc_ref(v_mctx_97_);
lean_dec(v___x_95_);
v_lctx_98_ = lean_ctor_get(v___y_86_, 2);
v_options_99_ = lean_ctor_get(v_toCold_96_, 2);
lean_inc_ref(v_options_99_);
lean_inc_ref(v_lctx_98_);
v___x_100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_100_, 0, v_env_94_);
lean_ctor_set(v___x_100_, 1, v_mctx_97_);
lean_ctor_set(v___x_100_, 2, v_lctx_98_);
lean_ctor_set(v___x_100_, 3, v_options_99_);
v___x_101_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_msgData_85_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___boxed(lean_object* v_msgData_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3(v_msgData_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(lean_object* v_msg_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_ref_118_; lean_object* v_macroStack_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_a_122_; lean_object* v___x_123_; lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_132_; 
v_ref_118_ = lean_ctor_get(v___y_115_, 2);
v_macroStack_119_ = lean_ctor_get(v___y_111_, 1);
v___x_120_ = l_Lean_Elab_getBetterRef(v_ref_118_, v_macroStack_119_);
v___x_121_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3(v_msg_110_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
lean_dec_ref(v___x_121_);
lean_inc(v_macroStack_119_);
v___x_123_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg(v_a_122_, v_macroStack_119_, v___y_115_);
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_132_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_120_);
lean_ctor_set(v___x_128_, 1, v_a_124_);
if (v_isShared_127_ == 0)
{
lean_ctor_set_tag(v___x_126_, 1);
lean_ctor_set(v___x_126_, 0, v___x_128_);
v___x_130_ = v___x_126_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg___boxed(lean_object* v_msg_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v_msg_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___redArg___lam__0(lean_object* v_stx_142_, lean_object* v_output_143_, lean_object* v_trees_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_lctx_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_lctx_152_ = lean_ctor_get(v___y_147_, 2);
lean_inc_ref(v_lctx_152_);
v___x_153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_153_, 0, v_lctx_152_);
lean_ctor_set(v___x_153_, 1, v_stx_142_);
lean_ctor_set(v___x_153_, 2, v_output_143_);
v___x_154_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_trees_144_);
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_stx_157_, lean_object* v_output_158_, lean_object* v_trees_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___redArg___lam__0(v_stx_157_, v_output_158_, v_trees_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
return v_res_167_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_unsigned_to_nat(32u);
v___x_169_ = lean_mk_empty_array_with_capacity(v___x_168_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_171_ = ((size_t)5ULL);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_unsigned_to_nat(32u);
v___x_174_ = lean_mk_empty_array_with_capacity(v___x_173_);
v___x_175_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_176_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
lean_ctor_set(v___x_176_, 2, v___x_172_);
lean_ctor_set(v___x_176_, 3, v___x_172_);
lean_ctor_set_usize(v___x_176_, 4, v___x_171_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; lean_object* v_infoState_180_; lean_object* v_trees_181_; lean_object* v___x_182_; lean_object* v_infoState_183_; lean_object* v_env_184_; lean_object* v_nextMacroScope_185_; lean_object* v_ngen_186_; lean_object* v_auxDeclNGen_187_; lean_object* v_traceState_188_; lean_object* v_cache_189_; lean_object* v_recordedDeps_190_; lean_object* v_messages_191_; lean_object* v_snapshotTasks_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_213_; 
v___x_179_ = lean_st_ref_get(v___y_177_);
v_infoState_180_ = lean_ctor_get(v___x_179_, 8);
lean_inc_ref(v_infoState_180_);
lean_dec(v___x_179_);
v_trees_181_ = lean_ctor_get(v_infoState_180_, 2);
lean_inc_ref(v_trees_181_);
lean_dec_ref(v_infoState_180_);
v___x_182_ = lean_st_ref_take(v___y_177_);
v_infoState_183_ = lean_ctor_get(v___x_182_, 8);
v_env_184_ = lean_ctor_get(v___x_182_, 0);
v_nextMacroScope_185_ = lean_ctor_get(v___x_182_, 1);
v_ngen_186_ = lean_ctor_get(v___x_182_, 2);
v_auxDeclNGen_187_ = lean_ctor_get(v___x_182_, 3);
v_traceState_188_ = lean_ctor_get(v___x_182_, 4);
v_cache_189_ = lean_ctor_get(v___x_182_, 5);
v_recordedDeps_190_ = lean_ctor_get(v___x_182_, 6);
v_messages_191_ = lean_ctor_get(v___x_182_, 7);
v_snapshotTasks_192_ = lean_ctor_get(v___x_182_, 9);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_213_ == 0)
{
v___x_194_ = v___x_182_;
v_isShared_195_ = v_isSharedCheck_213_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_snapshotTasks_192_);
lean_inc(v_infoState_183_);
lean_inc(v_messages_191_);
lean_inc(v_recordedDeps_190_);
lean_inc(v_cache_189_);
lean_inc(v_traceState_188_);
lean_inc(v_auxDeclNGen_187_);
lean_inc(v_ngen_186_);
lean_inc(v_nextMacroScope_185_);
lean_inc(v_env_184_);
lean_dec(v___x_182_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_213_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
uint8_t v_enabled_196_; lean_object* v_assignment_197_; lean_object* v_lazyAssignment_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_211_; 
v_enabled_196_ = lean_ctor_get_uint8(v_infoState_183_, sizeof(void*)*3);
v_assignment_197_ = lean_ctor_get(v_infoState_183_, 0);
v_lazyAssignment_198_ = lean_ctor_get(v_infoState_183_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v_infoState_183_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_infoState_183_, 2);
lean_dec(v_unused_212_);
v___x_200_ = v_infoState_183_;
v_isShared_201_ = v_isSharedCheck_211_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_lazyAssignment_198_);
lean_inc(v_assignment_197_);
lean_dec(v_infoState_183_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_211_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 2, v___x_202_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_assignment_197_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_lazyAssignment_198_);
lean_ctor_set(v_reuseFailAlloc_210_, 2, v___x_202_);
lean_ctor_set_uint8(v_reuseFailAlloc_210_, sizeof(void*)*3, v_enabled_196_);
v___x_204_ = v_reuseFailAlloc_210_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_206_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 8, v___x_204_);
v___x_206_ = v___x_194_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_env_184_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_nextMacroScope_185_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v_ngen_186_);
lean_ctor_set(v_reuseFailAlloc_209_, 3, v_auxDeclNGen_187_);
lean_ctor_set(v_reuseFailAlloc_209_, 4, v_traceState_188_);
lean_ctor_set(v_reuseFailAlloc_209_, 5, v_cache_189_);
lean_ctor_set(v_reuseFailAlloc_209_, 6, v_recordedDeps_190_);
lean_ctor_set(v_reuseFailAlloc_209_, 7, v_messages_191_);
lean_ctor_set(v_reuseFailAlloc_209_, 8, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_209_, 9, v_snapshotTasks_192_);
v___x_206_ = v_reuseFailAlloc_209_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_st_ref_put(v___y_177_, v___x_206_);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v_trees_181_);
return v___x_208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg(v___y_214_);
lean_dec(v___y_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg___lam__0(lean_object* v___y_217_, lean_object* v_mkInfoTree_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v_a_224_, lean_object* v_a_x3f_225_){
_start:
{
lean_object* v___x_227_; lean_object* v_infoState_228_; lean_object* v_trees_229_; lean_object* v___x_230_; 
v___x_227_ = lean_st_ref_get(v___y_217_);
v_infoState_228_ = lean_ctor_get(v___x_227_, 8);
lean_inc_ref(v_infoState_228_);
lean_dec(v___x_227_);
v_trees_229_ = lean_ctor_get(v_infoState_228_, 2);
lean_inc_ref(v_trees_229_);
lean_dec_ref(v_infoState_228_);
lean_inc(v___y_217_);
lean_inc_ref(v___y_223_);
lean_inc(v___y_222_);
lean_inc_ref(v___y_221_);
lean_inc(v___y_220_);
lean_inc_ref(v___y_219_);
v___x_230_ = lean_apply_8(v_mkInfoTree_218_, v_trees_229_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_217_, lean_box(0));
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_270_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_270_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_270_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_270_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v_infoState_236_; lean_object* v_env_237_; lean_object* v_nextMacroScope_238_; lean_object* v_ngen_239_; lean_object* v_auxDeclNGen_240_; lean_object* v_traceState_241_; lean_object* v_cache_242_; lean_object* v_recordedDeps_243_; lean_object* v_messages_244_; lean_object* v_snapshotTasks_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_269_; 
v___x_235_ = lean_st_ref_take(v___y_217_);
v_infoState_236_ = lean_ctor_get(v___x_235_, 8);
v_env_237_ = lean_ctor_get(v___x_235_, 0);
v_nextMacroScope_238_ = lean_ctor_get(v___x_235_, 1);
v_ngen_239_ = lean_ctor_get(v___x_235_, 2);
v_auxDeclNGen_240_ = lean_ctor_get(v___x_235_, 3);
v_traceState_241_ = lean_ctor_get(v___x_235_, 4);
v_cache_242_ = lean_ctor_get(v___x_235_, 5);
v_recordedDeps_243_ = lean_ctor_get(v___x_235_, 6);
v_messages_244_ = lean_ctor_get(v___x_235_, 7);
v_snapshotTasks_245_ = lean_ctor_get(v___x_235_, 9);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_269_ == 0)
{
v___x_247_ = v___x_235_;
v_isShared_248_ = v_isSharedCheck_269_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_snapshotTasks_245_);
lean_inc(v_infoState_236_);
lean_inc(v_messages_244_);
lean_inc(v_recordedDeps_243_);
lean_inc(v_cache_242_);
lean_inc(v_traceState_241_);
lean_inc(v_auxDeclNGen_240_);
lean_inc(v_ngen_239_);
lean_inc(v_nextMacroScope_238_);
lean_inc(v_env_237_);
lean_dec(v___x_235_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_269_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
uint8_t v_enabled_249_; lean_object* v_assignment_250_; lean_object* v_lazyAssignment_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_267_; 
v_enabled_249_ = lean_ctor_get_uint8(v_infoState_236_, sizeof(void*)*3);
v_assignment_250_ = lean_ctor_get(v_infoState_236_, 0);
v_lazyAssignment_251_ = lean_ctor_get(v_infoState_236_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_infoState_236_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v_infoState_236_, 2);
lean_dec(v_unused_268_);
v___x_253_ = v_infoState_236_;
v_isShared_254_ = v_isSharedCheck_267_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_lazyAssignment_251_);
lean_inc(v_assignment_250_);
lean_dec(v_infoState_236_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_267_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_255_ = lean_box(0);
v___x_256_ = l_Lean_PersistentArray_push___redArg(v_a_224_, v_a_231_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 2, v___x_256_);
v___x_258_ = v___x_253_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_assignment_250_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_lazyAssignment_251_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v___x_256_);
lean_ctor_set_uint8(v_reuseFailAlloc_266_, sizeof(void*)*3, v_enabled_249_);
v___x_258_ = v_reuseFailAlloc_266_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 8, v___x_258_);
v___x_260_ = v___x_247_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_env_237_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_nextMacroScope_238_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_ngen_239_);
lean_ctor_set(v_reuseFailAlloc_265_, 3, v_auxDeclNGen_240_);
lean_ctor_set(v_reuseFailAlloc_265_, 4, v_traceState_241_);
lean_ctor_set(v_reuseFailAlloc_265_, 5, v_cache_242_);
lean_ctor_set(v_reuseFailAlloc_265_, 6, v_recordedDeps_243_);
lean_ctor_set(v_reuseFailAlloc_265_, 7, v_messages_244_);
lean_ctor_set(v_reuseFailAlloc_265_, 8, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_265_, 9, v_snapshotTasks_245_);
v___x_260_ = v_reuseFailAlloc_265_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = lean_st_ref_put(v___y_217_, v___x_260_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_255_);
v___x_263_ = v___x_233_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_255_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec_ref(v_a_224_);
v_a_271_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_230_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_230_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v___y_279_, lean_object* v_mkInfoTree_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v_a_286_, lean_object* v_a_x3f_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg___lam__0(v___y_279_, v_mkInfoTree_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v_a_286_, v_a_x3f_287_);
lean_dec(v_a_x3f_287_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_279_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg(lean_object* v_x_290_, lean_object* v_mkInfoTree_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; lean_object* v_infoState_300_; uint8_t v_enabled_301_; 
v___x_299_ = lean_st_ref_get(v___y_297_);
v_infoState_300_ = lean_ctor_get(v___x_299_, 8);
lean_inc_ref(v_infoState_300_);
lean_dec(v___x_299_);
v_enabled_301_ = lean_ctor_get_uint8(v_infoState_300_, sizeof(void*)*3);
lean_dec_ref(v_infoState_300_);
if (v_enabled_301_ == 0)
{
lean_object* v___x_302_; 
lean_dec_ref(v_mkInfoTree_291_);
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
v___x_302_ = lean_apply_7(v_x_290_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, lean_box(0));
return v___x_302_;
}
else
{
lean_object* v___x_303_; lean_object* v_a_304_; lean_object* v_r_305_; 
v___x_303_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg(v___y_297_);
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref(v___x_303_);
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
v_r_305_ = lean_apply_7(v_x_290_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, lean_box(0));
if (lean_obj_tag(v_r_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_330_; 
v_a_306_ = lean_ctor_get(v_r_305_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v_r_305_);
if (v_isSharedCheck_330_ == 0)
{
v___x_308_ = v_r_305_;
v_isShared_309_ = v_isSharedCheck_330_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v_r_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_330_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
lean_inc(v_a_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 1);
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_329_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg___lam__0(v___y_297_, v_mkInfoTree_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v_a_304_, v___x_311_);
lean_dec_ref(v___x_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v___x_312_, 0);
lean_dec(v_unused_320_);
v___x_314_ = v___x_312_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_dec(v___x_312_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v_a_306_);
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_306_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec(v_a_306_);
v_a_321_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_312_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_312_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_a_331_ = lean_ctor_get(v_r_305_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v_r_305_, 1);
v___x_332_ = lean_box(0);
v___x_333_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg___lam__0(v___y_297_, v_mkInfoTree_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v_a_304_, v___x_332_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; 
v_unused_341_ = lean_ctor_get(v___x_333_, 0);
lean_dec(v_unused_341_);
v___x_335_ = v___x_333_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_dec(v___x_333_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set_tag(v___x_335_, 1);
lean_ctor_set(v___x_335_, 0, v_a_331_);
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_331_);
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
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_a_331_);
v_a_342_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_333_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_333_);
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
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_350_, lean_object* v_mkInfoTree_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg(v_x_350_, v_mkInfoTree_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___redArg(lean_object* v_stx_360_, lean_object* v_output_361_, lean_object* v_x_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___f_370_; lean_object* v___x_371_; 
v___f_370_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_370_, 0, v_stx_360_);
lean_closure_set(v___f_370_, 1, v_output_361_);
v___x_371_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg(v_x_362_, v___f_370_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___redArg___boxed(lean_object* v_stx_372_, lean_object* v_output_373_, lean_object* v_x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___redArg(v_stx_372_, v_output_373_, v_x_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(lean_object* v_beforeStx_383_, lean_object* v_afterStx_384_, lean_object* v_x_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_declName_x3f_393_; lean_object* v_macroStack_394_; uint8_t v_mayPostpone_395_; uint8_t v_errToSorry_396_; lean_object* v_autoBoundImplicitContext_397_; lean_object* v_autoBoundImplicitForbidden_398_; lean_object* v_sectionVars_399_; lean_object* v_sectionFVars_400_; uint8_t v_implicitLambda_401_; uint8_t v_heedElabAsElim_402_; uint8_t v_isNoncomputableSection_403_; uint8_t v_isMetaSection_404_; uint8_t v_ignoreTCFailures_405_; uint8_t v_inPattern_406_; lean_object* v_tacSnap_x3f_407_; uint8_t v_saveRecAppSyntax_408_; uint8_t v_holesAsSyntheticOpaque_409_; lean_object* v_fixedTermElabs_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_declName_x3f_393_ = lean_ctor_get(v___y_386_, 0);
v_macroStack_394_ = lean_ctor_get(v___y_386_, 1);
v_mayPostpone_395_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*8);
v_errToSorry_396_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_397_ = lean_ctor_get(v___y_386_, 2);
v_autoBoundImplicitForbidden_398_ = lean_ctor_get(v___y_386_, 3);
v_sectionVars_399_ = lean_ctor_get(v___y_386_, 4);
v_sectionFVars_400_ = lean_ctor_get(v___y_386_, 5);
v_implicitLambda_401_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*8 + 2);
v_heedElabAsElim_402_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_403_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*8 + 4);
v_isMetaSection_404_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_405_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*8 + 6);
v_inPattern_406_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_407_ = lean_ctor_get(v___y_386_, 6);
v_saveRecAppSyntax_408_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_409_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*8 + 9);
v_fixedTermElabs_410_ = lean_ctor_get(v___y_386_, 7);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v_beforeStx_383_);
lean_ctor_set(v___x_411_, 1, v_afterStx_384_);
lean_inc(v_macroStack_394_);
v___x_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_macroStack_394_);
lean_inc_ref(v_fixedTermElabs_410_);
lean_inc(v_tacSnap_x3f_407_);
lean_inc(v_sectionFVars_400_);
lean_inc(v_sectionVars_399_);
lean_inc_ref(v_autoBoundImplicitForbidden_398_);
lean_inc(v_autoBoundImplicitContext_397_);
lean_inc(v_declName_x3f_393_);
v___x_413_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_413_, 0, v_declName_x3f_393_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
lean_ctor_set(v___x_413_, 2, v_autoBoundImplicitContext_397_);
lean_ctor_set(v___x_413_, 3, v_autoBoundImplicitForbidden_398_);
lean_ctor_set(v___x_413_, 4, v_sectionVars_399_);
lean_ctor_set(v___x_413_, 5, v_sectionFVars_400_);
lean_ctor_set(v___x_413_, 6, v_tacSnap_x3f_407_);
lean_ctor_set(v___x_413_, 7, v_fixedTermElabs_410_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*8, v_mayPostpone_395_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*8 + 1, v_errToSorry_396_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*8 + 2, v_implicitLambda_401_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*8 + 3, v_heedElabAsElim_402_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*8 + 4, v_isNoncomputableSection_403_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*8 + 5, v_isMetaSection_404_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*8 + 6, v_ignoreTCFailures_405_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*8 + 7, v_inPattern_406_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_408_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_409_);
lean_inc(v___y_391_);
lean_inc_ref(v___y_390_);
lean_inc(v___y_389_);
lean_inc_ref(v___y_388_);
lean_inc(v___y_387_);
v___x_414_ = lean_apply_7(v_x_385_, v___x_413_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, lean_box(0));
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___boxed(lean_object* v_beforeStx_415_, lean_object* v_afterStx_416_, lean_object* v_x_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_beforeStx_415_, v_afterStx_416_, v_x_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0(lean_object* v_00_u03b1_426_, lean_object* v_beforeStx_427_, lean_object* v_afterStx_428_, lean_object* v_x_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_beforeStx_427_, v_afterStx_428_, v_x_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_438_, lean_object* v_beforeStx_439_, lean_object* v_afterStx_440_, lean_object* v_x_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0(v_00_u03b1_438_, v_beforeStx_439_, v_afterStx_440_, v_x_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(lean_object* v_beforeStx_450_, lean_object* v_afterStx_451_, lean_object* v_x_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc(v_afterStx_451_);
lean_inc(v_beforeStx_450_);
v___x_460_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___boxed), 11, 4);
lean_closure_set(v___x_460_, 0, lean_box(0));
lean_closure_set(v___x_460_, 1, v_beforeStx_450_);
lean_closure_set(v___x_460_, 2, v_afterStx_451_);
lean_closure_set(v___x_460_, 3, v_x_452_);
v___x_461_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___redArg(v_beforeStx_450_, v_afterStx_451_, v___x_460_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
v_a_470_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_461_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_461_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg___boxed(lean_object* v_beforeStx_478_, lean_object* v_afterStx_479_, lean_object* v_x_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_beforeStx_478_, v_afterStx_479_, v_x_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v_res_488_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5));
v___x_501_ = l_Lake_DSL_packageDeclName;
v___x_502_ = l_Lean_Name_str___override(v___x_501_, v___x_500_);
return v___x_502_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6, &l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6);
v___x_504_ = l_Lean_mkIdent(v___x_503_);
return v___x_504_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8));
v___x_507_ = l_Lean_stringToMessageData(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst(lean_object* v_stx_508_, lean_object* v_expectedType_x3f_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_env_543_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___x_560_; uint8_t v___x_561_; uint8_t v___x_562_; 
v___x_540_ = lean_box(0);
v___x_541_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4));
v___x_542_ = lean_st_ref_get(v_a_515_);
v_env_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc_ref_n(v_env_543_, 2);
lean_dec(v___x_542_);
v___x_560_ = l_Lake_DSL_packageDeclName;
v___x_561_ = 1;
v___x_562_ = l_Lean_Environment_contains(v_env_543_, v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec_ref(v_env_543_);
lean_dec(v_expectedType_x3f_509_);
lean_dec(v_stx_508_);
v___x_563_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9, &l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9);
v___x_564_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v___x_563_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
v___y_545_ = v_a_510_;
v___y_546_ = v_a_511_;
v___y_547_ = v_a_512_;
v___y_548_ = v_a_513_;
v___y_549_ = v_a_514_;
v___y_550_ = v_a_515_;
goto v___jp_544_;
}
v___jp_517_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_526_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3));
v___x_527_ = l_Nat_reprFast(v___y_522_);
v___x_528_ = lean_box(2);
v___x_529_ = l_Lean_Syntax_mkNumLit(v___x_527_, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(2u);
v___x_531_ = lean_mk_empty_array_with_capacity(v___x_530_);
v___x_532_ = lean_array_push(v___x_531_, v___y_525_);
v___x_533_ = lean_array_push(v___x_532_, v___x_529_);
v___x_534_ = l_Lean_Syntax_mkCApp(v___x_526_, v___x_533_);
v___x_535_ = 1;
v___x_536_ = lean_box(v___x_535_);
v___x_537_ = lean_box(v___x_535_);
lean_inc(v___x_534_);
v___x_538_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_538_, 0, v___x_534_);
lean_closure_set(v___x_538_, 1, v_expectedType_x3f_509_);
lean_closure_set(v___x_538_, 2, v___x_536_);
lean_closure_set(v___x_538_, 3, v___x_537_);
v___x_539_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_508_, v___x_534_, v___x_538_, v___y_519_, v___y_524_, v___y_521_, v___y_520_, v___y_518_, v___y_523_);
return v___x_539_;
}
v___jp_544_:
{
lean_object* v___x_551_; lean_object* v_asyncMode_552_; uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v_snd_555_; 
v___x_551_ = l_Lake_nameExt;
v_asyncMode_552_ = lean_ctor_get(v___x_551_, 2);
v___x_553_ = 0;
v___x_554_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_541_, v___x_551_, v_env_543_, v_asyncMode_552_, v___x_540_, v___x_553_);
v_snd_555_ = lean_ctor_get(v___x_554_, 1);
if (lean_obj_tag(v_snd_555_) == 0)
{
lean_object* v_fst_556_; lean_object* v___x_557_; 
v_fst_556_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_fst_556_);
lean_dec(v___x_554_);
v___x_557_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7, &l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7);
v___y_518_ = v___y_549_;
v___y_519_ = v___y_545_;
v___y_520_ = v___y_548_;
v___y_521_ = v___y_547_;
v___y_522_ = v_fst_556_;
v___y_523_ = v___y_550_;
v___y_524_ = v___y_546_;
v___y_525_ = v___x_557_;
goto v___jp_517_;
}
else
{
lean_object* v_fst_558_; lean_object* v___x_559_; 
lean_inc(v_snd_555_);
v_fst_558_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_fst_558_);
lean_dec(v___x_554_);
lean_inc(v_stx_508_);
v___x_559_ = l_Lake_Name_quoteFrom(v_stx_508_, v_snd_555_, v___x_553_);
v___y_518_ = v___y_549_;
v___y_519_ = v___y_545_;
v___y_520_ = v___y_548_;
v___y_521_ = v___y_547_;
v___y_522_ = v_fst_558_;
v___y_523_ = v___y_550_;
v___y_524_ = v___y_546_;
v___y_525_ = v___x_559_;
goto v___jp_517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___boxed(lean_object* v_stx_573_, lean_object* v_expectedType_x3f_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst(v_stx_573_, v_expectedType_x3f_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0(lean_object* v_00_u03b1_583_, lean_object* v_beforeStx_584_, lean_object* v_afterStx_585_, lean_object* v_x_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_beforeStx_584_, v_afterStx_585_, v_x_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___boxed(lean_object* v_00_u03b1_595_, lean_object* v_beforeStx_596_, lean_object* v_afterStx_597_, lean_object* v_x_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0(v_00_u03b1_595_, v_beforeStx_596_, v_afterStx_597_, v_x_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1(lean_object* v_00_u03b1_607_, lean_object* v_msg_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v_msg_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___boxed(lean_object* v_00_u03b1_617_, lean_object* v_msg_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1(v_00_u03b1_617_, v_msg_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1(lean_object* v_00_u03b1_627_, lean_object* v_stx_628_, lean_object* v_output_629_, lean_object* v_x_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___redArg(v_stx_628_, v_output_629_, v_x_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1___boxed(lean_object* v_00_u03b1_639_, lean_object* v_stx_640_, lean_object* v_output_641_, lean_object* v_x_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1(v_00_u03b1_639_, v_stx_640_, v_output_641_, v_x_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4(lean_object* v_msgData_651_, lean_object* v_macroStack_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___redArg(v_msgData_651_, v_macroStack_652_, v___y_657_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4___boxed(lean_object* v_msgData_661_, lean_object* v_macroStack_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__4(v_msgData_661_, v_macroStack_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5(lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___redArg(v___y_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2_spec__5(v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_687_, lean_object* v_x_688_, lean_object* v_mkInfoTree_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___redArg(v_x_688_, v_mkInfoTree_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_698_, lean_object* v_x_699_, lean_object* v_mkInfoTree_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__1_spec__2(v_00_u03b1_698_, v_x_699_, v_mkInfoTree_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1(){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_744_ = l_Lean_Elab_Term_termElabAttribute;
v___x_745_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3));
v___x_746_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14));
v___x_747_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___boxed), 9, 0);
v___x_748_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_744_, v___x_745_, v___x_746_, v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___boxed(lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1();
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst(lean_object* v_stx_768_, lean_object* v_expectedType_x3f_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___y_780_; lean_object* v_env_786_; lean_object* v___x_787_; lean_object* v_asyncMode_788_; lean_object* v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; 
v___x_777_ = lean_box(0);
v___x_778_ = lean_st_ref_get(v_a_775_);
v_env_786_ = lean_ctor_get(v___x_778_, 0);
lean_inc_ref(v_env_786_);
lean_dec(v___x_778_);
v___x_787_ = l_Lake_dirExt;
v_asyncMode_788_ = lean_ctor_get(v___x_787_, 2);
v___x_789_ = lean_box(0);
v___x_790_ = 0;
v___x_791_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_777_, v___x_787_, v_env_786_, v_asyncMode_788_, v___x_789_, v___x_790_);
if (lean_obj_tag(v___x_791_) == 1)
{
lean_object* v_val_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_val_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_val_792_);
lean_dec_ref_known(v___x_791_, 1);
v___x_793_ = l_Lean_SourceInfo_fromRef(v_stx_768_, v___x_790_);
v___x_794_ = l_Lean_Syntax_mkStrLit(v_val_792_, v___x_793_);
v___x_795_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3));
v___x_796_ = l_Lean_mkCIdentFrom(v_stx_768_, v___x_795_, v___x_790_);
v___x_797_ = lean_unsigned_to_nat(1u);
v___x_798_ = lean_mk_empty_array_with_capacity(v___x_797_);
v___x_799_ = lean_array_push(v___x_798_, v___x_794_);
v___x_800_ = l_Lean_Syntax_mkApp(v___x_796_, v___x_799_);
v___y_780_ = v___x_800_;
goto v___jp_779_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec(v___x_791_);
v___x_801_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5));
v___x_802_ = l_Lean_mkCIdentFrom(v_stx_768_, v___x_801_, v___x_790_);
v___x_803_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7));
v___x_804_ = l_Lean_mkCIdentFrom(v_stx_768_, v___x_803_, v___x_790_);
v___x_805_ = lean_unsigned_to_nat(1u);
v___x_806_ = lean_mk_empty_array_with_capacity(v___x_805_);
v___x_807_ = lean_array_push(v___x_806_, v___x_804_);
v___x_808_ = l_Lean_Syntax_mkApp(v___x_802_, v___x_807_);
v___y_780_ = v___x_808_;
goto v___jp_779_;
}
v___jp_779_:
{
uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_781_ = 1;
v___x_782_ = lean_box(v___x_781_);
v___x_783_ = lean_box(v___x_781_);
lean_inc(v___y_780_);
v___x_784_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_784_, 0, v___y_780_);
lean_closure_set(v___x_784_, 1, v_expectedType_x3f_769_);
lean_closure_set(v___x_784_, 2, v___x_782_);
lean_closure_set(v___x_784_, 3, v___x_783_);
v___x_785_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_768_, v___y_780_, v___x_784_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___boxed(lean_object* v_stx_809_, lean_object* v_expectedType_x3f_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst(v_stx_809_, v_expectedType_x3f_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1(){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_829_ = l_Lean_Elab_Term_termElabAttribute;
v___x_830_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1));
v___x_831_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3));
v___x_832_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___boxed), 9, 0);
v___x_833_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_829_, v___x_830_, v___x_831_, v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___boxed(lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1();
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f___redArg(){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = lean_box(0);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f___redArg___boxed(lean_object* v___dummy_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lake_DSL_dummyGetConfig_x3f___redArg();
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f(lean_object* v_a_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_box(0);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f___boxed(lean_object* v_a_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lake_DSL_dummyGetConfig_x3f(v_a_842_);
lean_dec(v_a_842_);
return v_res_843_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_box(0);
v___x_845_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___x_844_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg(){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___boxed(lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0(lean_object* v_00_u03b1_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___boxed(lean_object* v_00_u03b1_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0(v_00_u03b1_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
return v_res_869_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6));
v___x_885_ = l_String_toRawSubstring_x27(v___x_884_);
return v___x_885_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = ((lean_object*)(l_Lake_DSL_dummyDir___closed__0));
v___x_918_ = l_String_toRawSubstring_x27(v___x_917_);
return v___x_918_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36));
v___x_954_ = l_String_toRawSubstring_x27(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9));
v___x_968_ = l_String_toRawSubstring_x27(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52));
v___x_992_ = l_String_toRawSubstring_x27(v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig(lean_object* v_stx_1028_, lean_object* v_expectedType_x3f_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_box(0);
lean_inc(v_expectedType_x3f_1029_);
v___x_1038_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v___x_1039_; uint8_t v___x_1040_; lean_object* v_a_1042_; 
lean_dec_ref_known(v___x_1038_, 1);
v___x_1039_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1));
lean_inc(v_stx_1028_);
v___x_1040_ = l_Lean_Syntax_isOfKind(v_stx_1028_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1047_; 
lean_dec(v_expectedType_x3f_1029_);
lean_dec(v_stx_1028_);
v___x_1047_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_env_1051_; lean_object* v___x_1052_; lean_object* v_asyncMode_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; 
v___x_1048_ = lean_unsigned_to_nat(1u);
v___x_1049_ = l_Lean_Syntax_getArg(v_stx_1028_, v___x_1048_);
v___x_1050_ = lean_st_ref_get(v_a_1035_);
v_env_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc_ref(v_env_1051_);
lean_dec(v___x_1050_);
v___x_1052_ = l_Lake_optsExt;
v_asyncMode_1053_ = lean_ctor_get(v___x_1052_, 2);
v___x_1054_ = lean_box(0);
v___x_1055_ = 0;
v___x_1056_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1037_, v___x_1052_, v_env_1051_, v_asyncMode_1053_, v___x_1054_, v___x_1055_);
if (lean_obj_tag(v___x_1056_) == 1)
{
lean_object* v_val_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_val_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_val_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___x_1058_ = l_Lean_TSyntax_getId(v___x_1049_);
lean_dec(v___x_1049_);
v___x_1059_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_1057_, v___x_1058_);
lean_dec(v___x_1058_);
lean_dec(v_val_1057_);
if (lean_obj_tag(v___x_1059_) == 1)
{
lean_object* v_toCold_1060_; lean_object* v_val_1061_; lean_object* v_ref_1062_; lean_object* v_quotContext_1063_; lean_object* v_currMacroScope_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_toCold_1060_ = lean_ctor_get(v_a_1034_, 0);
v_val_1061_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_val_1061_);
lean_dec_ref_known(v___x_1059_, 1);
v_ref_1062_ = lean_ctor_get(v_a_1034_, 2);
v_quotContext_1063_ = lean_ctor_get(v_toCold_1060_, 8);
v_currMacroScope_1064_ = lean_ctor_get(v_toCold_1060_, 9);
v___x_1065_ = l_Lean_SourceInfo_fromRef(v_ref_1062_, v___x_1055_);
v___x_1066_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5));
v___x_1067_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7);
v___x_1068_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8));
lean_inc(v_currMacroScope_1064_);
lean_inc(v_quotContext_1063_);
v___x_1069_ = l_Lean_addMacroScope(v_quotContext_1063_, v___x_1068_, v_currMacroScope_1064_);
v___x_1070_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12));
lean_inc_n(v___x_1065_, 3);
v___x_1071_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1065_);
lean_ctor_set(v___x_1071_, 1, v___x_1067_);
lean_ctor_set(v___x_1071_, 2, v___x_1069_);
lean_ctor_set(v___x_1071_, 3, v___x_1070_);
v___x_1072_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14));
v___x_1073_ = l_Lean_Syntax_mkStrLit(v_val_1061_, v___x_1065_);
v___x_1074_ = l_Lean_Syntax_node1(v___x_1065_, v___x_1072_, v___x_1073_);
v___x_1075_ = l_Lean_Syntax_node2(v___x_1065_, v___x_1066_, v___x_1071_, v___x_1074_);
v_a_1042_ = v___x_1075_;
goto v___jp_1041_;
}
else
{
lean_object* v_toCold_1076_; lean_object* v_ref_1077_; lean_object* v_quotContext_1078_; lean_object* v_currMacroScope_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v___x_1059_);
v_toCold_1076_ = lean_ctor_get(v_a_1034_, 0);
v_ref_1077_ = lean_ctor_get(v_a_1034_, 2);
v_quotContext_1078_ = lean_ctor_get(v_toCold_1076_, 8);
v_currMacroScope_1079_ = lean_ctor_get(v_toCold_1076_, 9);
v___x_1080_ = l_Lean_SourceInfo_fromRef(v_ref_1077_, v___x_1055_);
v___x_1081_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16));
v___x_1082_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18));
v___x_1083_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19));
lean_inc_n(v___x_1080_, 12);
v___x_1084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1080_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21));
v___x_1086_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22);
lean_inc_n(v_currMacroScope_1079_, 4);
lean_inc_n(v_quotContext_1078_, 4);
v___x_1087_ = l_Lean_addMacroScope(v_quotContext_1078_, v___x_1054_, v_currMacroScope_1079_);
v___x_1088_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35));
v___x_1089_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1080_);
lean_ctor_set(v___x_1089_, 1, v___x_1086_);
lean_ctor_set(v___x_1089_, 2, v___x_1087_);
lean_ctor_set(v___x_1089_, 3, v___x_1088_);
v___x_1090_ = l_Lean_Syntax_node1(v___x_1080_, v___x_1085_, v___x_1089_);
v___x_1091_ = l_Lean_Syntax_node2(v___x_1080_, v___x_1082_, v___x_1084_, v___x_1090_);
v___x_1092_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37);
v___x_1093_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38));
v___x_1094_ = l_Lean_addMacroScope(v_quotContext_1078_, v___x_1093_, v_currMacroScope_1079_);
v___x_1095_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41));
v___x_1096_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1080_);
lean_ctor_set(v___x_1096_, 1, v___x_1092_);
lean_ctor_set(v___x_1096_, 2, v___x_1094_);
lean_ctor_set(v___x_1096_, 3, v___x_1095_);
v___x_1097_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42));
v___x_1098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1080_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14));
v___x_1100_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5));
v___x_1101_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43);
v___x_1102_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44));
v___x_1103_ = l_Lean_addMacroScope(v_quotContext_1078_, v___x_1102_, v_currMacroScope_1079_);
v___x_1104_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51));
v___x_1105_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1080_);
lean_ctor_set(v___x_1105_, 1, v___x_1101_);
lean_ctor_set(v___x_1105_, 2, v___x_1103_);
lean_ctor_set(v___x_1105_, 3, v___x_1104_);
v___x_1106_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53);
v___x_1107_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54));
v___x_1108_ = l_Lean_addMacroScope(v_quotContext_1078_, v___x_1107_, v_currMacroScope_1079_);
v___x_1109_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61));
v___x_1110_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1080_);
lean_ctor_set(v___x_1110_, 1, v___x_1106_);
lean_ctor_set(v___x_1110_, 2, v___x_1108_);
lean_ctor_set(v___x_1110_, 3, v___x_1109_);
v___x_1111_ = l_Lean_Syntax_node1(v___x_1080_, v___x_1099_, v___x_1110_);
v___x_1112_ = l_Lean_Syntax_node2(v___x_1080_, v___x_1100_, v___x_1105_, v___x_1111_);
v___x_1113_ = l_Lean_Syntax_node1(v___x_1080_, v___x_1099_, v___x_1112_);
v___x_1114_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62));
v___x_1115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1080_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = l_Lean_Syntax_node5(v___x_1080_, v___x_1081_, v___x_1091_, v___x_1096_, v___x_1098_, v___x_1113_, v___x_1115_);
v_a_1042_ = v___x_1116_;
goto v___jp_1041_;
}
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___y_1120_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec(v___x_1056_);
v___x_1117_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64));
v___x_1118_ = l_Lean_mkCIdentFrom(v_stx_1028_, v___x_1117_, v___x_1055_);
v___x_1124_ = l_Lean_TSyntax_getId(v___x_1049_);
lean_dec(v___x_1049_);
v___x_1125_ = lean_box(0);
lean_inc(v___x_1124_);
v___x_1126_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1125_, v___x_1124_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_quoteNameMk(v___x_1124_);
v___y_1120_ = v___x_1127_;
goto v___jp_1119_;
}
else
{
lean_object* v_val_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec(v___x_1124_);
v_val_1128_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_val_1128_);
lean_dec_ref_known(v___x_1126_, 1);
v___x_1129_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__66));
v___x_1130_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__67));
v___x_1131_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__68));
v___x_1132_ = lean_string_intercalate(v___x_1131_, v_val_1128_);
v___x_1133_ = lean_string_append(v___x_1130_, v___x_1132_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = lean_box(2);
v___x_1135_ = l_Lean_Syntax_mkNameLit(v___x_1133_, v___x_1134_);
v___x_1136_ = lean_mk_empty_array_with_capacity(v___x_1048_);
v___x_1137_ = lean_array_push(v___x_1136_, v___x_1135_);
v___x_1138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1134_);
lean_ctor_set(v___x_1138_, 1, v___x_1129_);
lean_ctor_set(v___x_1138_, 2, v___x_1137_);
v___y_1120_ = v___x_1138_;
goto v___jp_1119_;
}
v___jp_1119_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_mk_empty_array_with_capacity(v___x_1048_);
v___x_1122_ = lean_array_push(v___x_1121_, v___y_1120_);
v___x_1123_ = l_Lean_Syntax_mkApp(v___x_1118_, v___x_1122_);
v_a_1042_ = v___x_1123_;
goto v___jp_1041_;
}
}
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1043_ = lean_box(v___x_1040_);
v___x_1044_ = lean_box(v___x_1040_);
lean_inc(v_a_1042_);
v___x_1045_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_1045_, 0, v_a_1042_);
lean_closure_set(v___x_1045_, 1, v_expectedType_x3f_1029_);
lean_closure_set(v___x_1045_, 2, v___x_1043_);
lean_closure_set(v___x_1045_, 3, v___x_1044_);
v___x_1046_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_1028_, v_a_1042_, v___x_1045_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
return v___x_1046_;
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec(v_expectedType_x3f_1029_);
lean_dec(v_stx_1028_);
v_a_1139_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1038_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1038_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___boxed(lean_object* v_stx_1147_, lean_object* v_expectedType_x3f_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig(v_stx_1147_, v_expectedType_x3f_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1(){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1162_ = l_Lean_Elab_Term_termElabAttribute;
v___x_1163_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1));
v___x_1164_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1));
v___x_1165_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___boxed), 9, 0);
v___x_1166_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1162_, v___x_1163_, v___x_1164_, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___boxed(lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1();
return v_res_1168_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Extensions(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Config(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_Config(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Lake_DSL_Extensions(uint8_t builtin);
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* initialize_Lake_Util_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Config(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_Config(builtin);
}
#ifdef __cplusplus
}
#endif
