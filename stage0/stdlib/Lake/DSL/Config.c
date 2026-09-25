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
lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref_known(v_val_8_, 0);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_box(1);
v___x_16_ = l_Lean_MessageData_ofFormat(v___x_15_);
return v___x_16_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__2));
v___x_21_ = l_Lean_MessageData_ofFormat(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
return v_x_22_;
}
else
{
lean_object* v_head_24_; lean_object* v_tail_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_47_; 
v_head_24_ = lean_ctor_get(v_x_23_, 0);
v_tail_25_ = lean_ctor_get(v_x_23_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v_x_23_);
if (v_isSharedCheck_47_ == 0)
{
v___x_27_ = v_x_23_;
v_isShared_28_ = v_isSharedCheck_47_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_tail_25_);
lean_inc(v_head_24_);
lean_dec(v_x_23_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_47_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_before_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_45_; 
v_before_29_ = lean_ctor_get(v_head_24_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v_head_24_);
if (v_isSharedCheck_45_ == 0)
{
lean_object* v_unused_46_; 
v_unused_46_ = lean_ctor_get(v_head_24_, 1);
lean_dec(v_unused_46_);
v___x_31_ = v_head_24_;
v_isShared_32_ = v_isSharedCheck_45_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_before_29_);
lean_dec(v_head_24_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_45_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_33_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0);
if (v_isShared_32_ == 0)
{
lean_ctor_set_tag(v___x_31_, 7);
lean_ctor_set(v___x_31_, 1, v___x_33_);
lean_ctor_set(v___x_31_, 0, v_x_22_);
v___x_35_ = v___x_31_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_x_22_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v___x_33_);
v___x_35_ = v_reuseFailAlloc_44_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__3);
if (v_isShared_28_ == 0)
{
lean_ctor_set_tag(v___x_27_, 7);
lean_ctor_set(v___x_27_, 1, v___x_36_);
lean_ctor_set(v___x_27_, 0, v___x_35_);
v___x_38_ = v___x_27_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v___x_36_);
v___x_38_ = v_reuseFailAlloc_43_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = l_Lean_MessageData_ofSyntax(v_before_29_);
v___x_40_ = l_Lean_indentD(v___x_39_);
v___x_41_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_38_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
v_x_22_ = v___x_41_;
v_x_23_ = v_tail_25_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__1));
v___x_52_ = l_Lean_MessageData_ofFormat(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(lean_object* v_msgData_53_, lean_object* v_macroStack_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_57_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_55_);
v___x_58_ = l_Lean_Elab_pp_macroStack;
v___x_59_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5(v___x_57_, v___x_58_);
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
v___x_67_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6___closed__0);
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
v___x_70_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___closed__2);
v___x_71_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = l_Lean_MessageData_ofSyntax(v_after_63_);
v___x_73_ = l_Lean_indentD(v___x_72_);
v_msgData_74_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_74_, 0, v___x_71_);
lean_ctor_set(v_msgData_74_, 1, v___x_73_);
v___x_75_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__6(v_msgData_74_, v_macroStack_54_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_80_, lean_object* v_macroStack_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(v_msgData_80_, v_macroStack_81_, v___y_82_);
lean_dec_ref(v___y_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2(lean_object* v_msgData_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_env_92_; lean_object* v___x_93_; lean_object* v_toCold_94_; lean_object* v_mctx_95_; lean_object* v_lctx_96_; lean_object* v_options_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_91_ = lean_st_ref_get(v___y_89_);
v_env_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_env_92_);
lean_dec(v___x_91_);
v___x_93_ = lean_st_ref_get(v___y_87_);
v_toCold_94_ = lean_ctor_get(v___y_88_, 0);
v_mctx_95_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_mctx_95_);
lean_dec(v___x_93_);
v_lctx_96_ = lean_ctor_get(v___y_86_, 2);
v_options_97_ = lean_ctor_get(v_toCold_94_, 2);
lean_inc_ref(v_options_97_);
lean_inc_ref(v_lctx_96_);
v___x_98_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_98_, 0, v_env_92_);
lean_ctor_set(v___x_98_, 1, v_mctx_95_);
lean_ctor_set(v___x_98_, 2, v_lctx_96_);
lean_ctor_set(v___x_98_, 3, v_options_97_);
v___x_99_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_msgData_85_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2___boxed(lean_object* v_msgData_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2(v_msgData_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_ref_116_; lean_object* v_macroStack_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_a_120_; lean_object* v___x_121_; lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_130_; 
v_ref_116_ = lean_ctor_get(v___y_113_, 2);
v_macroStack_117_ = lean_ctor_get(v___y_109_, 1);
v___x_118_ = l_Lean_Elab_getBetterRef(v_ref_116_, v_macroStack_117_);
v___x_119_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2(v_msg_108_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
lean_dec_ref(v___x_119_);
lean_inc(v_macroStack_117_);
v___x_121_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(v_a_120_, v_macroStack_117_, v___y_113_);
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_130_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_118_);
lean_ctor_set(v___x_126_, 1, v_a_122_);
if (v_isShared_125_ == 0)
{
lean_ctor_set_tag(v___x_124_, 1);
lean_ctor_set(v___x_124_, 0, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg___boxed(lean_object* v_msg_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v_msg_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0(lean_object* v_stx_140_, lean_object* v_output_141_, lean_object* v_trees_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_lctx_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_lctx_150_ = lean_ctor_get(v___y_145_, 2);
lean_inc_ref(v_lctx_150_);
v___x_151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_151_, 0, v_lctx_150_);
lean_ctor_set(v___x_151_, 1, v_stx_140_);
lean_ctor_set(v___x_151_, 2, v_output_141_);
v___x_152_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
v___x_153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v_trees_142_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_stx_155_, lean_object* v_output_156_, lean_object* v_trees_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0(v_stx_155_, v_output_156_, v_trees_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
return v_res_165_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_unsigned_to_nat(32u);
v___x_167_ = lean_mk_empty_array_with_capacity(v___x_166_);
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_169_ = ((size_t)5ULL);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_unsigned_to_nat(32u);
v___x_172_ = lean_mk_empty_array_with_capacity(v___x_171_);
v___x_173_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
v___x_174_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
lean_ctor_set(v___x_174_, 2, v___x_170_);
lean_ctor_set(v___x_174_, 3, v___x_170_);
lean_ctor_set_usize(v___x_174_, 4, v___x_169_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; lean_object* v_infoState_178_; lean_object* v_trees_179_; lean_object* v___x_180_; lean_object* v_infoState_181_; lean_object* v_env_182_; lean_object* v_nextMacroScope_183_; lean_object* v_ngen_184_; lean_object* v_auxDeclNGen_185_; lean_object* v_traceState_186_; lean_object* v_cache_187_; lean_object* v_recordedDeps_188_; lean_object* v_messages_189_; lean_object* v_snapshotTasks_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_211_; 
v___x_177_ = lean_st_ref_get(v___y_175_);
v_infoState_178_ = lean_ctor_get(v___x_177_, 8);
lean_inc_ref(v_infoState_178_);
lean_dec(v___x_177_);
v_trees_179_ = lean_ctor_get(v_infoState_178_, 2);
lean_inc_ref(v_trees_179_);
lean_dec_ref(v_infoState_178_);
v___x_180_ = lean_st_ref_take(v___y_175_);
v_infoState_181_ = lean_ctor_get(v___x_180_, 8);
v_env_182_ = lean_ctor_get(v___x_180_, 0);
v_nextMacroScope_183_ = lean_ctor_get(v___x_180_, 1);
v_ngen_184_ = lean_ctor_get(v___x_180_, 2);
v_auxDeclNGen_185_ = lean_ctor_get(v___x_180_, 3);
v_traceState_186_ = lean_ctor_get(v___x_180_, 4);
v_cache_187_ = lean_ctor_get(v___x_180_, 5);
v_recordedDeps_188_ = lean_ctor_get(v___x_180_, 6);
v_messages_189_ = lean_ctor_get(v___x_180_, 7);
v_snapshotTasks_190_ = lean_ctor_get(v___x_180_, 9);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_211_ == 0)
{
v___x_192_ = v___x_180_;
v_isShared_193_ = v_isSharedCheck_211_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_snapshotTasks_190_);
lean_inc(v_infoState_181_);
lean_inc(v_messages_189_);
lean_inc(v_recordedDeps_188_);
lean_inc(v_cache_187_);
lean_inc(v_traceState_186_);
lean_inc(v_auxDeclNGen_185_);
lean_inc(v_ngen_184_);
lean_inc(v_nextMacroScope_183_);
lean_inc(v_env_182_);
lean_dec(v___x_180_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_211_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
uint8_t v_enabled_194_; lean_object* v_assignment_195_; lean_object* v_lazyAssignment_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_209_; 
v_enabled_194_ = lean_ctor_get_uint8(v_infoState_181_, sizeof(void*)*3);
v_assignment_195_ = lean_ctor_get(v_infoState_181_, 0);
v_lazyAssignment_196_ = lean_ctor_get(v_infoState_181_, 1);
v_isSharedCheck_209_ = !lean_is_exclusive(v_infoState_181_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v_infoState_181_, 2);
lean_dec(v_unused_210_);
v___x_198_ = v_infoState_181_;
v_isShared_199_ = v_isSharedCheck_209_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_lazyAssignment_196_);
lean_inc(v_assignment_195_);
lean_dec(v_infoState_181_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_209_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 2, v___x_200_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_assignment_195_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_lazyAssignment_196_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v___x_200_);
lean_ctor_set_uint8(v_reuseFailAlloc_208_, sizeof(void*)*3, v_enabled_194_);
v___x_202_ = v_reuseFailAlloc_208_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_204_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 8, v___x_202_);
v___x_204_ = v___x_192_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_env_182_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_nextMacroScope_183_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v_ngen_184_);
lean_ctor_set(v_reuseFailAlloc_207_, 3, v_auxDeclNGen_185_);
lean_ctor_set(v_reuseFailAlloc_207_, 4, v_traceState_186_);
lean_ctor_set(v_reuseFailAlloc_207_, 5, v_cache_187_);
lean_ctor_set(v_reuseFailAlloc_207_, 6, v_recordedDeps_188_);
lean_ctor_set(v_reuseFailAlloc_207_, 7, v_messages_189_);
lean_ctor_set(v_reuseFailAlloc_207_, 8, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_207_, 9, v_snapshotTasks_190_);
v___x_204_ = v_reuseFailAlloc_207_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_st_ref_put(v___y_175_, v___x_204_);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v_trees_179_);
return v___x_206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(v___y_212_);
lean_dec(v___y_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v___y_215_, lean_object* v_mkInfoTree_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v_a_222_, lean_object* v_a_x3f_223_){
_start:
{
lean_object* v___x_225_; lean_object* v_infoState_226_; lean_object* v_trees_227_; lean_object* v___x_228_; 
v___x_225_ = lean_st_ref_get(v___y_215_);
v_infoState_226_ = lean_ctor_get(v___x_225_, 8);
lean_inc_ref(v_infoState_226_);
lean_dec(v___x_225_);
v_trees_227_ = lean_ctor_get(v_infoState_226_, 2);
lean_inc_ref(v_trees_227_);
lean_dec_ref(v_infoState_226_);
lean_inc(v___y_215_);
lean_inc_ref(v___y_221_);
lean_inc(v___y_220_);
lean_inc_ref(v___y_219_);
lean_inc(v___y_218_);
lean_inc_ref(v___y_217_);
v___x_228_ = lean_apply_8(v_mkInfoTree_216_, v_trees_227_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_215_, lean_box(0));
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_268_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_268_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_268_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_268_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v_infoState_234_; lean_object* v_env_235_; lean_object* v_nextMacroScope_236_; lean_object* v_ngen_237_; lean_object* v_auxDeclNGen_238_; lean_object* v_traceState_239_; lean_object* v_cache_240_; lean_object* v_recordedDeps_241_; lean_object* v_messages_242_; lean_object* v_snapshotTasks_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_267_; 
v___x_233_ = lean_st_ref_take(v___y_215_);
v_infoState_234_ = lean_ctor_get(v___x_233_, 8);
v_env_235_ = lean_ctor_get(v___x_233_, 0);
v_nextMacroScope_236_ = lean_ctor_get(v___x_233_, 1);
v_ngen_237_ = lean_ctor_get(v___x_233_, 2);
v_auxDeclNGen_238_ = lean_ctor_get(v___x_233_, 3);
v_traceState_239_ = lean_ctor_get(v___x_233_, 4);
v_cache_240_ = lean_ctor_get(v___x_233_, 5);
v_recordedDeps_241_ = lean_ctor_get(v___x_233_, 6);
v_messages_242_ = lean_ctor_get(v___x_233_, 7);
v_snapshotTasks_243_ = lean_ctor_get(v___x_233_, 9);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_267_ == 0)
{
v___x_245_ = v___x_233_;
v_isShared_246_ = v_isSharedCheck_267_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_snapshotTasks_243_);
lean_inc(v_infoState_234_);
lean_inc(v_messages_242_);
lean_inc(v_recordedDeps_241_);
lean_inc(v_cache_240_);
lean_inc(v_traceState_239_);
lean_inc(v_auxDeclNGen_238_);
lean_inc(v_ngen_237_);
lean_inc(v_nextMacroScope_236_);
lean_inc(v_env_235_);
lean_dec(v___x_233_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_267_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
uint8_t v_enabled_247_; lean_object* v_assignment_248_; lean_object* v_lazyAssignment_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_265_; 
v_enabled_247_ = lean_ctor_get_uint8(v_infoState_234_, sizeof(void*)*3);
v_assignment_248_ = lean_ctor_get(v_infoState_234_, 0);
v_lazyAssignment_249_ = lean_ctor_get(v_infoState_234_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_infoState_234_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; 
v_unused_266_ = lean_ctor_get(v_infoState_234_, 2);
lean_dec(v_unused_266_);
v___x_251_ = v_infoState_234_;
v_isShared_252_ = v_isSharedCheck_265_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_lazyAssignment_249_);
lean_inc(v_assignment_248_);
lean_dec(v_infoState_234_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_265_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_253_ = lean_box(0);
v___x_254_ = l_Lean_PersistentArray_push___redArg(v_a_222_, v_a_229_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 2, v___x_254_);
v___x_256_ = v___x_251_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_assignment_248_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_lazyAssignment_249_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v___x_254_);
lean_ctor_set_uint8(v_reuseFailAlloc_264_, sizeof(void*)*3, v_enabled_247_);
v___x_256_ = v_reuseFailAlloc_264_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 8, v___x_256_);
v___x_258_ = v___x_245_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_env_235_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_nextMacroScope_236_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v_ngen_237_);
lean_ctor_set(v_reuseFailAlloc_263_, 3, v_auxDeclNGen_238_);
lean_ctor_set(v_reuseFailAlloc_263_, 4, v_traceState_239_);
lean_ctor_set(v_reuseFailAlloc_263_, 5, v_cache_240_);
lean_ctor_set(v_reuseFailAlloc_263_, 6, v_recordedDeps_241_);
lean_ctor_set(v_reuseFailAlloc_263_, 7, v_messages_242_);
lean_ctor_set(v_reuseFailAlloc_263_, 8, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_263_, 9, v_snapshotTasks_243_);
v___x_258_ = v_reuseFailAlloc_263_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = lean_st_ref_put(v___y_215_, v___x_258_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_253_);
v___x_261_ = v___x_231_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_253_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec_ref(v_a_222_);
v_a_269_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_228_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_228_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_277_, lean_object* v_mkInfoTree_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v_a_284_, lean_object* v_a_x3f_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(v___y_277_, v_mkInfoTree_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v_a_284_, v_a_x3f_285_);
lean_dec(v_a_x3f_285_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_277_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(lean_object* v_x_288_, lean_object* v_mkInfoTree_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_infoState_298_; uint8_t v_enabled_299_; 
v___x_297_ = lean_st_ref_get(v___y_295_);
v_infoState_298_ = lean_ctor_get(v___x_297_, 8);
lean_inc_ref(v_infoState_298_);
lean_dec(v___x_297_);
v_enabled_299_ = lean_ctor_get_uint8(v_infoState_298_, sizeof(void*)*3);
lean_dec_ref(v_infoState_298_);
if (v_enabled_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec_ref(v_mkInfoTree_289_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
lean_inc(v___y_291_);
lean_inc_ref(v___y_290_);
v___x_300_ = lean_apply_7(v_x_288_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, lean_box(0));
return v___x_300_;
}
else
{
lean_object* v___x_301_; lean_object* v_a_302_; lean_object* v_r_303_; 
v___x_301_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(v___y_295_);
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref(v___x_301_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
lean_inc(v___y_291_);
lean_inc_ref(v___y_290_);
v_r_303_ = lean_apply_7(v_x_288_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, lean_box(0));
if (lean_obj_tag(v_r_303_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_328_; 
v_a_304_ = lean_ctor_get(v_r_303_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_r_303_);
if (v_isSharedCheck_328_ == 0)
{
v___x_306_ = v_r_303_;
v_isShared_307_ = v_isSharedCheck_328_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v_r_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_328_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
lean_inc(v_a_304_);
if (v_isShared_307_ == 0)
{
lean_ctor_set_tag(v___x_306_, 1);
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_327_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(v___y_295_, v_mkInfoTree_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v_a_302_, v___x_309_);
lean_dec_ref(v___x_309_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v___x_310_, 0);
lean_dec(v_unused_318_);
v___x_312_ = v___x_310_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_dec(v___x_310_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v_a_304_);
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_304_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec(v_a_304_);
v_a_319_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_310_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_310_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_a_329_ = lean_ctor_get(v_r_303_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v_r_303_, 1);
v___x_330_ = lean_box(0);
v___x_331_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(v___y_295_, v_mkInfoTree_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v_a_302_, v___x_330_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; 
v_unused_339_ = lean_ctor_get(v___x_331_, 0);
lean_dec(v_unused_339_);
v___x_333_ = v___x_331_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_dec(v___x_331_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set_tag(v___x_333_, 1);
lean_ctor_set(v___x_333_, 0, v_a_329_);
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_329_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_a_329_);
v_a_340_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_331_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_331_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_348_, lean_object* v_mkInfoTree_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(v_x_348_, v_mkInfoTree_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(lean_object* v_stx_358_, lean_object* v_output_359_, lean_object* v_x_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___f_368_; lean_object* v___x_369_; 
v___f_368_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_368_, 0, v_stx_358_);
lean_closure_set(v___f_368_, 1, v_output_359_);
v___x_369_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(v_x_360_, v___f_368_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___boxed(lean_object* v_stx_370_, lean_object* v_output_371_, lean_object* v_x_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_stx_370_, v_output_371_, v_x_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(lean_object* v_beforeStx_381_, lean_object* v_afterStx_382_, lean_object* v_x_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_inc(v_afterStx_382_);
lean_inc(v_beforeStx_381_);
v___x_391_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_391_, 0, lean_box(0));
lean_closure_set(v___x_391_, 1, v_beforeStx_381_);
lean_closure_set(v___x_391_, 2, v_afterStx_382_);
lean_closure_set(v___x_391_, 3, v_x_383_);
v___x_392_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_beforeStx_381_, v_afterStx_382_, v___x_391_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
v_a_401_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_392_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_392_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg___boxed(lean_object* v_beforeStx_409_, lean_object* v_afterStx_410_, lean_object* v_x_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_beforeStx_409_, v_afterStx_410_, v_x_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_419_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5));
v___x_432_ = l_Lake_DSL_packageDeclName;
v___x_433_ = l_Lean_Name_str___override(v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6, &l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6);
v___x_435_ = l_Lean_mkIdent(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8));
v___x_438_ = l_Lean_stringToMessageData(v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst(lean_object* v_stx_439_, lean_object* v_expectedType_x3f_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_env_474_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___x_491_; uint8_t v___x_492_; uint8_t v___x_493_; 
v___x_471_ = lean_box(0);
v___x_472_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4));
v___x_473_ = lean_st_ref_get(v_a_446_);
v_env_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc_ref_n(v_env_474_, 2);
lean_dec(v___x_473_);
v___x_491_ = l_Lake_DSL_packageDeclName;
v___x_492_ = 1;
v___x_493_ = l_Lean_Environment_contains(v_env_474_, v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v_env_474_);
lean_dec(v_expectedType_x3f_440_);
lean_dec(v_stx_439_);
v___x_494_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9, &l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9);
v___x_495_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v___x_494_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
else
{
v___y_476_ = v_a_441_;
v___y_477_ = v_a_442_;
v___y_478_ = v_a_443_;
v___y_479_ = v_a_444_;
v___y_480_ = v_a_445_;
v___y_481_ = v_a_446_;
goto v___jp_475_;
}
v___jp_448_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_457_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3));
v___x_458_ = l_Nat_reprFast(v___y_453_);
v___x_459_ = lean_box(2);
v___x_460_ = l_Lean_Syntax_mkNumLit(v___x_458_, v___x_459_);
v___x_461_ = lean_unsigned_to_nat(2u);
v___x_462_ = lean_mk_empty_array_with_capacity(v___x_461_);
v___x_463_ = lean_array_push(v___x_462_, v___y_456_);
v___x_464_ = lean_array_push(v___x_463_, v___x_460_);
v___x_465_ = l_Lean_Syntax_mkCApp(v___x_457_, v___x_464_);
v___x_466_ = 1;
v___x_467_ = lean_box(v___x_466_);
v___x_468_ = lean_box(v___x_466_);
lean_inc(v___x_465_);
v___x_469_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_469_, 0, v___x_465_);
lean_closure_set(v___x_469_, 1, v_expectedType_x3f_440_);
lean_closure_set(v___x_469_, 2, v___x_467_);
lean_closure_set(v___x_469_, 3, v___x_468_);
v___x_470_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_439_, v___x_465_, v___x_469_, v___y_454_, v___y_452_, v___y_451_, v___y_450_, v___y_455_, v___y_449_);
return v___x_470_;
}
v___jp_475_:
{
lean_object* v___x_482_; lean_object* v_asyncMode_483_; lean_object* v___x_484_; lean_object* v_snd_485_; 
v___x_482_ = l_Lake_nameExt;
v_asyncMode_483_ = lean_ctor_get(v___x_482_, 2);
v___x_484_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_472_, v___x_482_, v_env_474_, v_asyncMode_483_, v___x_471_);
v_snd_485_ = lean_ctor_get(v___x_484_, 1);
lean_inc(v_snd_485_);
if (lean_obj_tag(v_snd_485_) == 0)
{
lean_object* v_fst_486_; lean_object* v___x_487_; 
v_fst_486_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_fst_486_);
lean_dec(v___x_484_);
v___x_487_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7, &l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7);
v___y_449_ = v___y_481_;
v___y_450_ = v___y_479_;
v___y_451_ = v___y_478_;
v___y_452_ = v___y_477_;
v___y_453_ = v_fst_486_;
v___y_454_ = v___y_476_;
v___y_455_ = v___y_480_;
v___y_456_ = v___x_487_;
goto v___jp_448_;
}
else
{
lean_object* v_fst_488_; uint8_t v___x_489_; lean_object* v___x_490_; 
v_fst_488_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_fst_488_);
lean_dec(v___x_484_);
v___x_489_ = 0;
lean_inc(v_stx_439_);
v___x_490_ = l_Lake_Name_quoteFrom(v_stx_439_, v_snd_485_, v___x_489_);
v___y_449_ = v___y_481_;
v___y_450_ = v___y_479_;
v___y_451_ = v___y_478_;
v___y_452_ = v___y_477_;
v___y_453_ = v_fst_488_;
v___y_454_ = v___y_476_;
v___y_455_ = v___y_480_;
v___y_456_ = v___x_490_;
goto v___jp_448_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___boxed(lean_object* v_stx_504_, lean_object* v_expectedType_x3f_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst(v_stx_504_, v_expectedType_x3f_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0(lean_object* v_00_u03b1_514_, lean_object* v_beforeStx_515_, lean_object* v_afterStx_516_, lean_object* v_x_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_beforeStx_515_, v_afterStx_516_, v_x_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___boxed(lean_object* v_00_u03b1_526_, lean_object* v_beforeStx_527_, lean_object* v_afterStx_528_, lean_object* v_x_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0(v_00_u03b1_526_, v_beforeStx_527_, v_afterStx_528_, v_x_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1(lean_object* v_00_u03b1_538_, lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v_msg_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___boxed(lean_object* v_00_u03b1_548_, lean_object* v_msg_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1(v_00_u03b1_548_, v_msg_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0(lean_object* v_00_u03b1_558_, lean_object* v_stx_559_, lean_object* v_output_560_, lean_object* v_x_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_stx_559_, v_output_560_, v_x_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_570_, lean_object* v_stx_571_, lean_object* v_output_572_, lean_object* v_x_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0(v_00_u03b1_570_, v_stx_571_, v_output_572_, v_x_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3(lean_object* v_msgData_582_, lean_object* v_macroStack_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(v_msgData_582_, v_macroStack_583_, v___y_588_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___boxed(lean_object* v_msgData_592_, lean_object* v_macroStack_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3(v_msgData_592_, v_macroStack_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4(lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(v___y_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4(v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_618_, lean_object* v_x_619_, lean_object* v_mkInfoTree_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(v_x_619_, v_mkInfoTree_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_629_, lean_object* v_x_630_, lean_object* v_mkInfoTree_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1(v_00_u03b1_629_, v_x_630_, v_mkInfoTree_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1(){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_675_ = l_Lean_Elab_Term_termElabAttribute;
v___x_676_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3));
v___x_677_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14));
v___x_678_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___boxed), 9, 0);
v___x_679_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_675_, v___x_676_, v___x_677_, v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___boxed(lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1();
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst(lean_object* v_stx_699_, lean_object* v_expectedType_x3f_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___y_711_; lean_object* v_env_717_; lean_object* v___x_718_; lean_object* v_asyncMode_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_708_ = lean_box(0);
v___x_709_ = lean_st_ref_get(v_a_706_);
v_env_717_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_env_717_);
lean_dec(v___x_709_);
v___x_718_ = l_Lake_dirExt;
v_asyncMode_719_ = lean_ctor_get(v___x_718_, 2);
v___x_720_ = lean_box(0);
v___x_721_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_708_, v___x_718_, v_env_717_, v_asyncMode_719_, v___x_720_);
if (lean_obj_tag(v___x_721_) == 1)
{
lean_object* v_val_722_; uint8_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_val_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_val_722_);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = 0;
v___x_724_ = l_Lean_SourceInfo_fromRef(v_stx_699_, v___x_723_);
v___x_725_ = l_Lean_Syntax_mkStrLit(v_val_722_, v___x_724_);
v___x_726_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3));
v___x_727_ = l_Lean_mkCIdentFrom(v_stx_699_, v___x_726_, v___x_723_);
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_mk_empty_array_with_capacity(v___x_728_);
v___x_730_ = lean_array_push(v___x_729_, v___x_725_);
v___x_731_ = l_Lean_Syntax_mkApp(v___x_727_, v___x_730_);
v___y_711_ = v___x_731_;
goto v___jp_710_;
}
else
{
lean_object* v___x_732_; uint8_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec(v___x_721_);
v___x_732_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5));
v___x_733_ = 0;
v___x_734_ = l_Lean_mkCIdentFrom(v_stx_699_, v___x_732_, v___x_733_);
v___x_735_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7));
v___x_736_ = l_Lean_mkCIdentFrom(v_stx_699_, v___x_735_, v___x_733_);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_mk_empty_array_with_capacity(v___x_737_);
v___x_739_ = lean_array_push(v___x_738_, v___x_736_);
v___x_740_ = l_Lean_Syntax_mkApp(v___x_734_, v___x_739_);
v___y_711_ = v___x_740_;
goto v___jp_710_;
}
v___jp_710_:
{
uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_712_ = 1;
v___x_713_ = lean_box(v___x_712_);
v___x_714_ = lean_box(v___x_712_);
lean_inc(v___y_711_);
v___x_715_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_715_, 0, v___y_711_);
lean_closure_set(v___x_715_, 1, v_expectedType_x3f_700_);
lean_closure_set(v___x_715_, 2, v___x_713_);
lean_closure_set(v___x_715_, 3, v___x_714_);
v___x_716_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_699_, v___y_711_, v___x_715_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___boxed(lean_object* v_stx_741_, lean_object* v_expectedType_x3f_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst(v_stx_741_, v_expectedType_x3f_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1(){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_761_ = l_Lean_Elab_Term_termElabAttribute;
v___x_762_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1));
v___x_763_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3));
v___x_764_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___boxed), 9, 0);
v___x_765_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_761_, v___x_762_, v___x_763_, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___boxed(lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1();
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f___redArg(){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = lean_box(0);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f___redArg___boxed(lean_object* v___dummy_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lake_DSL_dummyGetConfig_x3f___redArg();
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f(lean_object* v_a_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = lean_box(0);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f___boxed(lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lake_DSL_dummyGetConfig_x3f(v_a_774_);
lean_dec(v_a_774_);
return v_res_775_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_box(0);
v___x_777_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg(){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0);
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___boxed(lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0(lean_object* v_00_u03b1_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___boxed(lean_object* v_00_u03b1_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0(v_00_u03b1_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_801_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6));
v___x_817_ = l_String_toRawSubstring_x27(v___x_816_);
return v___x_817_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l_Lake_DSL_dummyDir___closed__0));
v___x_850_ = l_String_toRawSubstring_x27(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36));
v___x_886_ = l_String_toRawSubstring_x27(v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9));
v___x_900_ = l_String_toRawSubstring_x27(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52));
v___x_924_ = l_String_toRawSubstring_x27(v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig(lean_object* v_stx_960_, lean_object* v_expectedType_x3f_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_box(0);
lean_inc(v_expectedType_x3f_961_);
v___x_970_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v___x_971_; uint8_t v___x_972_; lean_object* v_a_974_; 
lean_dec_ref_known(v___x_970_, 1);
v___x_971_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1));
lean_inc(v_stx_960_);
v___x_972_ = l_Lean_Syntax_isOfKind(v_stx_960_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_979_; 
lean_dec(v_expectedType_x3f_961_);
lean_dec(v_stx_960_);
v___x_979_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
return v___x_979_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_env_983_; lean_object* v___x_984_; lean_object* v_asyncMode_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_980_ = lean_unsigned_to_nat(1u);
v___x_981_ = l_Lean_Syntax_getArg(v_stx_960_, v___x_980_);
v___x_982_ = lean_st_ref_get(v_a_967_);
v_env_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc_ref(v_env_983_);
lean_dec(v___x_982_);
v___x_984_ = l_Lake_optsExt;
v_asyncMode_985_ = lean_ctor_get(v___x_984_, 2);
v___x_986_ = lean_box(0);
v___x_987_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_969_, v___x_984_, v_env_983_, v_asyncMode_985_, v___x_986_);
if (lean_obj_tag(v___x_987_) == 1)
{
lean_object* v_val_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_val_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_val_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = l_Lean_TSyntax_getId(v___x_981_);
lean_dec(v___x_981_);
v___x_990_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_988_, v___x_989_);
lean_dec(v___x_989_);
lean_dec(v_val_988_);
if (lean_obj_tag(v___x_990_) == 1)
{
lean_object* v_toCold_991_; lean_object* v_val_992_; lean_object* v_ref_993_; lean_object* v_quotContext_994_; lean_object* v_currMacroScope_995_; uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_toCold_991_ = lean_ctor_get(v_a_966_, 0);
v_val_992_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v___x_990_, 1);
v_ref_993_ = lean_ctor_get(v_a_966_, 2);
v_quotContext_994_ = lean_ctor_get(v_toCold_991_, 8);
v_currMacroScope_995_ = lean_ctor_get(v_toCold_991_, 9);
v___x_996_ = 0;
v___x_997_ = l_Lean_SourceInfo_fromRef(v_ref_993_, v___x_996_);
v___x_998_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5));
v___x_999_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7);
v___x_1000_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8));
lean_inc(v_currMacroScope_995_);
lean_inc(v_quotContext_994_);
v___x_1001_ = l_Lean_addMacroScope(v_quotContext_994_, v___x_1000_, v_currMacroScope_995_);
v___x_1002_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12));
lean_inc_n(v___x_997_, 3);
v___x_1003_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1003_, 0, v___x_997_);
lean_ctor_set(v___x_1003_, 1, v___x_999_);
lean_ctor_set(v___x_1003_, 2, v___x_1001_);
lean_ctor_set(v___x_1003_, 3, v___x_1002_);
v___x_1004_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14));
v___x_1005_ = l_Lean_Syntax_mkStrLit(v_val_992_, v___x_997_);
v___x_1006_ = l_Lean_Syntax_node1(v___x_997_, v___x_1004_, v___x_1005_);
v___x_1007_ = l_Lean_Syntax_node2(v___x_997_, v___x_998_, v___x_1003_, v___x_1006_);
v_a_974_ = v___x_1007_;
goto v___jp_973_;
}
else
{
lean_object* v_toCold_1008_; lean_object* v_ref_1009_; lean_object* v_quotContext_1010_; lean_object* v_currMacroScope_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec(v___x_990_);
v_toCold_1008_ = lean_ctor_get(v_a_966_, 0);
v_ref_1009_ = lean_ctor_get(v_a_966_, 2);
v_quotContext_1010_ = lean_ctor_get(v_toCold_1008_, 8);
v_currMacroScope_1011_ = lean_ctor_get(v_toCold_1008_, 9);
v___x_1012_ = 0;
v___x_1013_ = l_Lean_SourceInfo_fromRef(v_ref_1009_, v___x_1012_);
v___x_1014_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16));
v___x_1015_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18));
v___x_1016_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19));
lean_inc_n(v___x_1013_, 12);
v___x_1017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1013_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21));
v___x_1019_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22);
lean_inc_n(v_currMacroScope_1011_, 4);
lean_inc_n(v_quotContext_1010_, 4);
v___x_1020_ = l_Lean_addMacroScope(v_quotContext_1010_, v___x_986_, v_currMacroScope_1011_);
v___x_1021_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35));
v___x_1022_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1013_);
lean_ctor_set(v___x_1022_, 1, v___x_1019_);
lean_ctor_set(v___x_1022_, 2, v___x_1020_);
lean_ctor_set(v___x_1022_, 3, v___x_1021_);
v___x_1023_ = l_Lean_Syntax_node1(v___x_1013_, v___x_1018_, v___x_1022_);
v___x_1024_ = l_Lean_Syntax_node2(v___x_1013_, v___x_1015_, v___x_1017_, v___x_1023_);
v___x_1025_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37);
v___x_1026_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38));
v___x_1027_ = l_Lean_addMacroScope(v_quotContext_1010_, v___x_1026_, v_currMacroScope_1011_);
v___x_1028_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41));
v___x_1029_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1013_);
lean_ctor_set(v___x_1029_, 1, v___x_1025_);
lean_ctor_set(v___x_1029_, 2, v___x_1027_);
lean_ctor_set(v___x_1029_, 3, v___x_1028_);
v___x_1030_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42));
v___x_1031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1013_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14));
v___x_1033_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5));
v___x_1034_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43);
v___x_1035_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44));
v___x_1036_ = l_Lean_addMacroScope(v_quotContext_1010_, v___x_1035_, v_currMacroScope_1011_);
v___x_1037_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51));
v___x_1038_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1013_);
lean_ctor_set(v___x_1038_, 1, v___x_1034_);
lean_ctor_set(v___x_1038_, 2, v___x_1036_);
lean_ctor_set(v___x_1038_, 3, v___x_1037_);
v___x_1039_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53);
v___x_1040_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54));
v___x_1041_ = l_Lean_addMacroScope(v_quotContext_1010_, v___x_1040_, v_currMacroScope_1011_);
v___x_1042_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61));
v___x_1043_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1013_);
lean_ctor_set(v___x_1043_, 1, v___x_1039_);
lean_ctor_set(v___x_1043_, 2, v___x_1041_);
lean_ctor_set(v___x_1043_, 3, v___x_1042_);
v___x_1044_ = l_Lean_Syntax_node1(v___x_1013_, v___x_1032_, v___x_1043_);
v___x_1045_ = l_Lean_Syntax_node2(v___x_1013_, v___x_1033_, v___x_1038_, v___x_1044_);
v___x_1046_ = l_Lean_Syntax_node1(v___x_1013_, v___x_1032_, v___x_1045_);
v___x_1047_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62));
v___x_1048_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1013_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = l_Lean_Syntax_node5(v___x_1013_, v___x_1014_, v___x_1024_, v___x_1029_, v___x_1031_, v___x_1046_, v___x_1048_);
v_a_974_ = v___x_1049_;
goto v___jp_973_;
}
}
else
{
lean_object* v___x_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___y_1054_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec(v___x_987_);
v___x_1050_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64));
v___x_1051_ = 0;
v___x_1052_ = l_Lean_mkCIdentFrom(v_stx_960_, v___x_1050_, v___x_1051_);
v___x_1058_ = l_Lean_TSyntax_getId(v___x_981_);
lean_dec(v___x_981_);
v___x_1059_ = lean_box(0);
lean_inc(v___x_1058_);
v___x_1060_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1059_, v___x_1058_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_quoteNameMk(v___x_1058_);
v___y_1054_ = v___x_1061_;
goto v___jp_1053_;
}
else
{
lean_object* v_val_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_dec(v___x_1058_);
v_val_1062_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_val_1062_);
lean_dec_ref_known(v___x_1060_, 1);
v___x_1063_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__66));
v___x_1064_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__67));
v___x_1065_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__68));
v___x_1066_ = lean_string_intercalate(v___x_1065_, v_val_1062_);
v___x_1067_ = lean_string_append(v___x_1064_, v___x_1066_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = lean_box(2);
v___x_1069_ = l_Lean_Syntax_mkNameLit(v___x_1067_, v___x_1068_);
v___x_1070_ = lean_mk_empty_array_with_capacity(v___x_980_);
v___x_1071_ = lean_array_push(v___x_1070_, v___x_1069_);
v___x_1072_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1068_);
lean_ctor_set(v___x_1072_, 1, v___x_1063_);
lean_ctor_set(v___x_1072_, 2, v___x_1071_);
v___y_1054_ = v___x_1072_;
goto v___jp_1053_;
}
v___jp_1053_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1055_ = lean_mk_empty_array_with_capacity(v___x_980_);
v___x_1056_ = lean_array_push(v___x_1055_, v___y_1054_);
v___x_1057_ = l_Lean_Syntax_mkApp(v___x_1052_, v___x_1056_);
v_a_974_ = v___x_1057_;
goto v___jp_973_;
}
}
}
v___jp_973_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_975_ = lean_box(v___x_972_);
v___x_976_ = lean_box(v___x_972_);
lean_inc(v_a_974_);
v___x_977_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_977_, 0, v_a_974_);
lean_closure_set(v___x_977_, 1, v_expectedType_x3f_961_);
lean_closure_set(v___x_977_, 2, v___x_975_);
lean_closure_set(v___x_977_, 3, v___x_976_);
v___x_978_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_960_, v_a_974_, v___x_977_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
return v___x_978_;
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_expectedType_x3f_961_);
lean_dec(v_stx_960_);
v_a_1073_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_970_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_970_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___boxed(lean_object* v_stx_1081_, lean_object* v_expectedType_x3f_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig(v_stx_1081_, v_expectedType_x3f_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1(){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1096_ = l_Lean_Elab_Term_termElabAttribute;
v___x_1097_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1));
v___x_1098_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1));
v___x_1099_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___boxed), 9, 0);
v___x_1100_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1096_, v___x_1097_, v___x_1098_, v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___boxed(lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1();
return v_res_1102_;
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
