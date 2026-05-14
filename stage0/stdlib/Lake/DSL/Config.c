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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
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
extern lean_object* l_Lake_optsExt;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
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
lean_object* lean_mk_syntax_ident(lean_object*);
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
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__56_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__55_value),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__57_value)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dummyGetConfig\?"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__60_value),LEAN_SCALAR_PTR_LITERAL(43, 158, 45, 71, 114, 122, 16, 88)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62_value;
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_0),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_1),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value_aux_2),((lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__62_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64_value;
static const lean_string_object l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65 = (const lean_object*)&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65_value;
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
lean_dec_ref(v___x_6_);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref(v_val_8_);
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
lean_object* v_options_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v_options_57_ = lean_ctor_get(v___y_55_, 2);
v___x_58_ = l_Lean_Elab_pp_macroStack;
v___x_59_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3_spec__5(v_options_57_, v___x_58_);
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
lean_object* v___x_91_; lean_object* v_env_92_; lean_object* v___x_93_; lean_object* v_mctx_94_; lean_object* v_lctx_95_; lean_object* v_options_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_91_ = lean_st_ref_get(v___y_89_);
v_env_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_env_92_);
lean_dec(v___x_91_);
v___x_93_ = lean_st_ref_get(v___y_87_);
v_mctx_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_mctx_94_);
lean_dec(v___x_93_);
v_lctx_95_ = lean_ctor_get(v___y_86_, 2);
v_options_96_ = lean_ctor_get(v___y_88_, 2);
lean_inc_ref(v_options_96_);
lean_inc_ref(v_lctx_95_);
v___x_97_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_97_, 0, v_env_92_);
lean_ctor_set(v___x_97_, 1, v_mctx_94_);
lean_ctor_set(v___x_97_, 2, v_lctx_95_);
lean_ctor_set(v___x_97_, 3, v_options_96_);
v___x_98_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v_msgData_85_);
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2___boxed(lean_object* v_msgData_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2(v_msgData_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(lean_object* v_msg_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_ref_115_; lean_object* v___x_116_; lean_object* v_a_117_; lean_object* v_macroStack_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_ref_115_ = lean_ctor_get(v___y_112_, 5);
v___x_116_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__2(v_msg_107_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref(v___x_116_);
v_macroStack_118_ = lean_ctor_get(v___y_108_, 1);
v___x_119_ = l_Lean_Elab_getBetterRef(v_ref_115_, v_macroStack_118_);
lean_inc(v_macroStack_118_);
v___x_120_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(v_a_117_, v_macroStack_118_, v___y_112_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_119_);
lean_ctor_set(v___x_125_, 1, v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 1);
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg___boxed(lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0(lean_object* v_stx_139_, lean_object* v_output_140_, lean_object* v_trees_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_lctx_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_lctx_149_ = lean_ctor_get(v___y_144_, 2);
lean_inc_ref(v_lctx_149_);
v___x_150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_150_, 0, v_lctx_149_);
lean_ctor_set(v___x_150_, 1, v_stx_139_);
lean_ctor_set(v___x_150_, 2, v_output_140_);
v___x_151_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_trees_141_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_stx_154_, lean_object* v_output_155_, lean_object* v_trees_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0(v_stx_154_, v_output_155_, v_trees_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_164_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_unsigned_to_nat(32u);
v___x_166_ = lean_mk_empty_array_with_capacity(v___x_165_);
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_168_ = ((size_t)5ULL);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_unsigned_to_nat(32u);
v___x_171_ = lean_mk_empty_array_with_capacity(v___x_170_);
v___x_172_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
v___x_173_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___x_171_);
lean_ctor_set(v___x_173_, 2, v___x_169_);
lean_ctor_set(v___x_173_, 3, v___x_169_);
lean_ctor_set_usize(v___x_173_, 4, v___x_168_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; lean_object* v_infoState_177_; lean_object* v_trees_178_; lean_object* v___x_179_; lean_object* v_infoState_180_; lean_object* v_env_181_; lean_object* v_nextMacroScope_182_; lean_object* v_ngen_183_; lean_object* v_auxDeclNGen_184_; lean_object* v_traceState_185_; lean_object* v_cache_186_; lean_object* v_messages_187_; lean_object* v_snapshotTasks_188_; lean_object* v_newDecls_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_210_; 
v___x_176_ = lean_st_ref_get(v___y_174_);
v_infoState_177_ = lean_ctor_get(v___x_176_, 7);
lean_inc_ref(v_infoState_177_);
lean_dec(v___x_176_);
v_trees_178_ = lean_ctor_get(v_infoState_177_, 2);
lean_inc_ref(v_trees_178_);
lean_dec_ref(v_infoState_177_);
v___x_179_ = lean_st_ref_take(v___y_174_);
v_infoState_180_ = lean_ctor_get(v___x_179_, 7);
v_env_181_ = lean_ctor_get(v___x_179_, 0);
v_nextMacroScope_182_ = lean_ctor_get(v___x_179_, 1);
v_ngen_183_ = lean_ctor_get(v___x_179_, 2);
v_auxDeclNGen_184_ = lean_ctor_get(v___x_179_, 3);
v_traceState_185_ = lean_ctor_get(v___x_179_, 4);
v_cache_186_ = lean_ctor_get(v___x_179_, 5);
v_messages_187_ = lean_ctor_get(v___x_179_, 6);
v_snapshotTasks_188_ = lean_ctor_get(v___x_179_, 8);
v_newDecls_189_ = lean_ctor_get(v___x_179_, 9);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_210_ == 0)
{
v___x_191_ = v___x_179_;
v_isShared_192_ = v_isSharedCheck_210_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_newDecls_189_);
lean_inc(v_snapshotTasks_188_);
lean_inc(v_infoState_180_);
lean_inc(v_messages_187_);
lean_inc(v_cache_186_);
lean_inc(v_traceState_185_);
lean_inc(v_auxDeclNGen_184_);
lean_inc(v_ngen_183_);
lean_inc(v_nextMacroScope_182_);
lean_inc(v_env_181_);
lean_dec(v___x_179_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_210_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
uint8_t v_enabled_193_; lean_object* v_assignment_194_; lean_object* v_lazyAssignment_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_208_; 
v_enabled_193_ = lean_ctor_get_uint8(v_infoState_180_, sizeof(void*)*3);
v_assignment_194_ = lean_ctor_get(v_infoState_180_, 0);
v_lazyAssignment_195_ = lean_ctor_get(v_infoState_180_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v_infoState_180_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; 
v_unused_209_ = lean_ctor_get(v_infoState_180_, 2);
lean_dec(v_unused_209_);
v___x_197_ = v_infoState_180_;
v_isShared_198_ = v_isSharedCheck_208_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_lazyAssignment_195_);
lean_inc(v_assignment_194_);
lean_dec(v_infoState_180_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_208_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 2, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_assignment_194_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_lazyAssignment_195_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v___x_199_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, sizeof(void*)*3, v_enabled_193_);
v___x_201_ = v_reuseFailAlloc_207_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_203_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 7, v___x_201_);
v___x_203_ = v___x_191_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_env_181_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_nextMacroScope_182_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_ngen_183_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v_auxDeclNGen_184_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v_traceState_185_);
lean_ctor_set(v_reuseFailAlloc_206_, 5, v_cache_186_);
lean_ctor_set(v_reuseFailAlloc_206_, 6, v_messages_187_);
lean_ctor_set(v_reuseFailAlloc_206_, 7, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_206_, 8, v_snapshotTasks_188_);
lean_ctor_set(v_reuseFailAlloc_206_, 9, v_newDecls_189_);
v___x_203_ = v_reuseFailAlloc_206_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_st_ref_set(v___y_174_, v___x_203_);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v_trees_178_);
return v___x_205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(v___y_211_);
lean_dec(v___y_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v___y_214_, lean_object* v_mkInfoTree_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v_a_221_, lean_object* v_a_x3f_222_){
_start:
{
lean_object* v___x_224_; lean_object* v_infoState_225_; lean_object* v_trees_226_; lean_object* v___x_227_; 
v___x_224_ = lean_st_ref_get(v___y_214_);
v_infoState_225_ = lean_ctor_get(v___x_224_, 7);
lean_inc_ref(v_infoState_225_);
lean_dec(v___x_224_);
v_trees_226_ = lean_ctor_get(v_infoState_225_, 2);
lean_inc_ref(v_trees_226_);
lean_dec_ref(v_infoState_225_);
lean_inc(v___y_214_);
lean_inc_ref(v___y_220_);
lean_inc(v___y_219_);
lean_inc_ref(v___y_218_);
lean_inc(v___y_217_);
lean_inc_ref(v___y_216_);
v___x_227_ = lean_apply_8(v_mkInfoTree_215_, v_trees_226_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_214_, lean_box(0));
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_267_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_267_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_267_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_267_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v_infoState_233_; lean_object* v_env_234_; lean_object* v_nextMacroScope_235_; lean_object* v_ngen_236_; lean_object* v_auxDeclNGen_237_; lean_object* v_traceState_238_; lean_object* v_cache_239_; lean_object* v_messages_240_; lean_object* v_snapshotTasks_241_; lean_object* v_newDecls_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_266_; 
v___x_232_ = lean_st_ref_take(v___y_214_);
v_infoState_233_ = lean_ctor_get(v___x_232_, 7);
v_env_234_ = lean_ctor_get(v___x_232_, 0);
v_nextMacroScope_235_ = lean_ctor_get(v___x_232_, 1);
v_ngen_236_ = lean_ctor_get(v___x_232_, 2);
v_auxDeclNGen_237_ = lean_ctor_get(v___x_232_, 3);
v_traceState_238_ = lean_ctor_get(v___x_232_, 4);
v_cache_239_ = lean_ctor_get(v___x_232_, 5);
v_messages_240_ = lean_ctor_get(v___x_232_, 6);
v_snapshotTasks_241_ = lean_ctor_get(v___x_232_, 8);
v_newDecls_242_ = lean_ctor_get(v___x_232_, 9);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_266_ == 0)
{
v___x_244_ = v___x_232_;
v_isShared_245_ = v_isSharedCheck_266_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_newDecls_242_);
lean_inc(v_snapshotTasks_241_);
lean_inc(v_infoState_233_);
lean_inc(v_messages_240_);
lean_inc(v_cache_239_);
lean_inc(v_traceState_238_);
lean_inc(v_auxDeclNGen_237_);
lean_inc(v_ngen_236_);
lean_inc(v_nextMacroScope_235_);
lean_inc(v_env_234_);
lean_dec(v___x_232_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_266_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
uint8_t v_enabled_246_; lean_object* v_assignment_247_; lean_object* v_lazyAssignment_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_264_; 
v_enabled_246_ = lean_ctor_get_uint8(v_infoState_233_, sizeof(void*)*3);
v_assignment_247_ = lean_ctor_get(v_infoState_233_, 0);
v_lazyAssignment_248_ = lean_ctor_get(v_infoState_233_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_infoState_233_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; 
v_unused_265_ = lean_ctor_get(v_infoState_233_, 2);
lean_dec(v_unused_265_);
v___x_250_ = v_infoState_233_;
v_isShared_251_ = v_isSharedCheck_264_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_lazyAssignment_248_);
lean_inc(v_assignment_247_);
lean_dec(v_infoState_233_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_264_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = l_Lean_PersistentArray_push___redArg(v_a_221_, v_a_228_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 2, v___x_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_assignment_247_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_lazyAssignment_248_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v___x_252_);
lean_ctor_set_uint8(v_reuseFailAlloc_263_, sizeof(void*)*3, v_enabled_246_);
v___x_254_ = v_reuseFailAlloc_263_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_256_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 7, v___x_254_);
v___x_256_ = v___x_244_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_env_234_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_nextMacroScope_235_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_ngen_236_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_auxDeclNGen_237_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v_traceState_238_);
lean_ctor_set(v_reuseFailAlloc_262_, 5, v_cache_239_);
lean_ctor_set(v_reuseFailAlloc_262_, 6, v_messages_240_);
lean_ctor_set(v_reuseFailAlloc_262_, 7, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_262_, 8, v_snapshotTasks_241_);
lean_ctor_set(v_reuseFailAlloc_262_, 9, v_newDecls_242_);
v___x_256_ = v_reuseFailAlloc_262_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_257_ = lean_st_ref_set(v___y_214_, v___x_256_);
v___x_258_ = lean_box(0);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_258_);
v___x_260_ = v___x_230_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_dec_ref(v_a_221_);
v_a_268_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_227_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_227_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_276_, lean_object* v_mkInfoTree_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v_a_283_, lean_object* v_a_x3f_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(v___y_276_, v_mkInfoTree_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v_a_283_, v_a_x3f_284_);
lean_dec(v_a_x3f_284_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_276_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(lean_object* v_x_287_, lean_object* v_mkInfoTree_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; lean_object* v_infoState_297_; uint8_t v_enabled_298_; 
v___x_296_ = lean_st_ref_get(v___y_294_);
v_infoState_297_ = lean_ctor_get(v___x_296_, 7);
lean_inc_ref(v_infoState_297_);
lean_dec(v___x_296_);
v_enabled_298_ = lean_ctor_get_uint8(v_infoState_297_, sizeof(void*)*3);
lean_dec_ref(v_infoState_297_);
if (v_enabled_298_ == 0)
{
lean_object* v___x_299_; 
lean_dec_ref(v_mkInfoTree_288_);
lean_inc(v___y_294_);
lean_inc_ref(v___y_293_);
lean_inc(v___y_292_);
lean_inc_ref(v___y_291_);
lean_inc(v___y_290_);
lean_inc_ref(v___y_289_);
v___x_299_ = lean_apply_7(v_x_287_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, lean_box(0));
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v_a_301_; lean_object* v_r_302_; 
v___x_300_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(v___y_294_);
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref(v___x_300_);
lean_inc(v___y_294_);
lean_inc_ref(v___y_293_);
lean_inc(v___y_292_);
lean_inc_ref(v___y_291_);
lean_inc(v___y_290_);
lean_inc_ref(v___y_289_);
v_r_302_ = lean_apply_7(v_x_287_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, lean_box(0));
if (lean_obj_tag(v_r_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_327_; 
v_a_303_ = lean_ctor_get(v_r_302_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_r_302_);
if (v_isSharedCheck_327_ == 0)
{
v___x_305_ = v_r_302_;
v_isShared_306_ = v_isSharedCheck_327_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v_r_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_327_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
lean_inc(v_a_303_);
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 1);
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_326_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(v___y_294_, v_mkInfoTree_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v_a_301_, v___x_308_);
lean_dec_ref(v___x_308_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; 
v_unused_317_ = lean_ctor_get(v___x_309_, 0);
lean_dec(v_unused_317_);
v___x_311_ = v___x_309_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_dec(v___x_309_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v_a_303_);
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_303_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec(v_a_303_);
v_a_318_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_309_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_309_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_a_328_ = lean_ctor_get(v_r_302_, 0);
lean_inc(v_a_328_);
lean_dec_ref(v_r_302_);
v___x_329_ = lean_box(0);
v___x_330_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___lam__0(v___y_294_, v_mkInfoTree_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v_a_301_, v___x_329_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v___x_330_, 0);
lean_dec(v_unused_338_);
v___x_332_ = v___x_330_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_dec(v___x_330_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 1);
lean_ctor_set(v___x_332_, 0, v_a_328_);
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_328_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_a_328_);
v_a_339_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_330_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_330_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_347_, lean_object* v_mkInfoTree_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(v_x_347_, v_mkInfoTree_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(lean_object* v_stx_357_, lean_object* v_output_358_, lean_object* v_x_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___f_367_; lean_object* v___x_368_; 
v___f_367_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_367_, 0, v_stx_357_);
lean_closure_set(v___f_367_, 1, v_output_358_);
v___x_368_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(v_x_359_, v___f_367_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg___boxed(lean_object* v_stx_369_, lean_object* v_output_370_, lean_object* v_x_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_stx_369_, v_output_370_, v_x_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(lean_object* v_beforeStx_380_, lean_object* v_afterStx_381_, lean_object* v_x_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_inc(v_afterStx_381_);
lean_inc(v_beforeStx_380_);
v___x_390_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_390_, 0, lean_box(0));
lean_closure_set(v___x_390_, 1, v_beforeStx_380_);
lean_closure_set(v___x_390_, 2, v_afterStx_381_);
lean_closure_set(v___x_390_, 3, v_x_382_);
v___x_391_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_beforeStx_380_, v_afterStx_381_, v___x_390_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
v_a_400_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_391_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_391_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg___boxed(lean_object* v_beforeStx_408_, lean_object* v_afterStx_409_, lean_object* v_x_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_beforeStx_408_, v_afterStx_409_, v_x_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_418_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__5));
v___x_431_ = l_Lake_DSL_packageDeclName;
v___x_432_ = l_Lean_Name_str___override(v___x_431_, v___x_430_);
return v___x_432_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6, &l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__6);
v___x_434_ = lean_mk_syntax_ident(v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__8));
v___x_437_ = l_Lean_stringToMessageData(v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst(lean_object* v_stx_438_, lean_object* v_expectedType_x3f_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___x_470_; lean_object* v_env_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___x_490_; uint8_t v___x_491_; uint8_t v___x_492_; 
v___x_470_ = lean_st_ref_get(v_a_445_);
v_env_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc_ref_n(v_env_471_, 2);
lean_dec(v___x_470_);
v___x_472_ = lean_box(0);
v___x_473_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__4));
v___x_490_ = l_Lake_DSL_packageDeclName;
v___x_491_ = 1;
v___x_492_ = l_Lean_Environment_contains(v_env_471_, v___x_490_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec_ref(v_env_471_);
lean_dec(v_expectedType_x3f_439_);
lean_dec(v_stx_438_);
v___x_493_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9, &l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__9);
v___x_494_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v___x_493_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
else
{
v___y_475_ = v_a_440_;
v___y_476_ = v_a_441_;
v___y_477_ = v_a_442_;
v___y_478_ = v_a_443_;
v___y_479_ = v_a_444_;
v___y_480_ = v_a_445_;
goto v___jp_474_;
}
v___jp_447_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_456_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__3));
v___x_457_ = l_Nat_reprFast(v___y_449_);
v___x_458_ = lean_box(2);
v___x_459_ = l_Lean_Syntax_mkNumLit(v___x_457_, v___x_458_);
v___x_460_ = lean_unsigned_to_nat(2u);
v___x_461_ = lean_mk_empty_array_with_capacity(v___x_460_);
v___x_462_ = lean_array_push(v___x_461_, v___y_455_);
v___x_463_ = lean_array_push(v___x_462_, v___x_459_);
v___x_464_ = l_Lean_Syntax_mkCApp(v___x_456_, v___x_463_);
v___x_465_ = 1;
v___x_466_ = lean_box(v___x_465_);
v___x_467_ = lean_box(v___x_465_);
lean_inc(v___x_464_);
v___x_468_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_468_, 0, v___x_464_);
lean_closure_set(v___x_468_, 1, v_expectedType_x3f_439_);
lean_closure_set(v___x_468_, 2, v___x_466_);
lean_closure_set(v___x_468_, 3, v___x_467_);
v___x_469_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_438_, v___x_464_, v___x_468_, v___y_450_, v___y_453_, v___y_452_, v___y_454_, v___y_451_, v___y_448_);
return v___x_469_;
}
v___jp_474_:
{
lean_object* v___x_481_; lean_object* v_asyncMode_482_; lean_object* v___x_483_; lean_object* v_snd_484_; 
v___x_481_ = l_Lake_nameExt;
v_asyncMode_482_ = lean_ctor_get(v___x_481_, 2);
v___x_483_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_473_, v___x_481_, v_env_471_, v_asyncMode_482_, v___x_472_);
v_snd_484_ = lean_ctor_get(v___x_483_, 1);
lean_inc(v_snd_484_);
if (lean_obj_tag(v_snd_484_) == 0)
{
lean_object* v_fst_485_; lean_object* v___x_486_; 
v_fst_485_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_fst_485_);
lean_dec(v___x_483_);
v___x_486_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7, &l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___closed__7);
v___y_448_ = v___y_480_;
v___y_449_ = v_fst_485_;
v___y_450_ = v___y_475_;
v___y_451_ = v___y_479_;
v___y_452_ = v___y_477_;
v___y_453_ = v___y_476_;
v___y_454_ = v___y_478_;
v___y_455_ = v___x_486_;
goto v___jp_447_;
}
else
{
lean_object* v_fst_487_; uint8_t v___x_488_; lean_object* v___x_489_; 
v_fst_487_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_fst_487_);
lean_dec(v___x_483_);
v___x_488_ = 0;
lean_inc(v_stx_438_);
v___x_489_ = l_Lake_Name_quoteFrom(v_stx_438_, v_snd_484_, v___x_488_);
v___y_448_ = v___y_480_;
v___y_449_ = v_fst_487_;
v___y_450_ = v___y_475_;
v___y_451_ = v___y_479_;
v___y_452_ = v___y_477_;
v___y_453_ = v___y_476_;
v___y_454_ = v___y_478_;
v___y_455_ = v___x_489_;
goto v___jp_447_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___boxed(lean_object* v_stx_503_, lean_object* v_expectedType_x3f_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst(v_stx_503_, v_expectedType_x3f_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0(lean_object* v_00_u03b1_513_, lean_object* v_beforeStx_514_, lean_object* v_afterStx_515_, lean_object* v_x_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_beforeStx_514_, v_afterStx_515_, v_x_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___boxed(lean_object* v_00_u03b1_525_, lean_object* v_beforeStx_526_, lean_object* v_afterStx_527_, lean_object* v_x_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0(v_00_u03b1_525_, v_beforeStx_526_, v_afterStx_527_, v_x_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1(lean_object* v_00_u03b1_537_, lean_object* v_msg_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___redArg(v_msg_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1___boxed(lean_object* v_00_u03b1_547_, lean_object* v_msg_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1(v_00_u03b1_547_, v_msg_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0(lean_object* v_00_u03b1_557_, lean_object* v_stx_558_, lean_object* v_output_559_, lean_object* v_x_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___redArg(v_stx_558_, v_output_559_, v_x_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_569_, lean_object* v_stx_570_, lean_object* v_output_571_, lean_object* v_x_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0(v_00_u03b1_569_, v_stx_570_, v_output_571_, v_x_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3(lean_object* v_msgData_581_, lean_object* v_macroStack_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___redArg(v_msgData_581_, v_macroStack_582_, v___y_587_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3___boxed(lean_object* v_msgData_591_, lean_object* v_macroStack_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__1_spec__3(v_msgData_591_, v_macroStack_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4(lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___redArg(v___y_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1_spec__4(v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_617_, lean_object* v_x_618_, lean_object* v_mkInfoTree_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___redArg(v_x_618_, v_mkInfoTree_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_628_, lean_object* v_x_629_, lean_object* v_mkInfoTree_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0_spec__0_spec__1(v_00_u03b1_628_, v_x_629_, v_mkInfoTree_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1(){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_674_ = l_Lean_Elab_Term_termElabAttribute;
v___x_675_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__3));
v___x_676_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___closed__14));
v___x_677_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___boxed), 9, 0);
v___x_678_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_674_, v___x_675_, v___x_676_, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1___boxed(lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabNameConst__1();
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst(lean_object* v_stx_698_, lean_object* v_expectedType_x3f_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v___x_707_; lean_object* v___y_709_; lean_object* v_env_715_; lean_object* v___x_716_; lean_object* v_asyncMode_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_707_ = lean_st_ref_get(v_a_705_);
v_env_715_ = lean_ctor_get(v___x_707_, 0);
lean_inc_ref(v_env_715_);
lean_dec(v___x_707_);
v___x_716_ = l_Lake_dirExt;
v_asyncMode_717_ = lean_ctor_get(v___x_716_, 2);
v___x_718_ = lean_box(0);
v___x_719_ = lean_box(0);
v___x_720_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_718_, v___x_716_, v_env_715_, v_asyncMode_717_, v___x_719_);
if (lean_obj_tag(v___x_720_) == 1)
{
lean_object* v_val_721_; uint8_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_val_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_val_721_);
lean_dec_ref(v___x_720_);
v___x_722_ = 0;
v___x_723_ = l_Lean_SourceInfo_fromRef(v_stx_698_, v___x_722_);
v___x_724_ = l_Lean_Syntax_mkStrLit(v_val_721_, v___x_723_);
v___x_725_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__3));
v___x_726_ = l_Lean_mkCIdentFrom(v_stx_698_, v___x_725_, v___x_722_);
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_mk_empty_array_with_capacity(v___x_727_);
v___x_729_ = lean_array_push(v___x_728_, v___x_724_);
v___x_730_ = l_Lean_Syntax_mkApp(v___x_726_, v___x_729_);
v___y_709_ = v___x_730_;
goto v___jp_708_;
}
else
{
lean_object* v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v___x_720_);
v___x_731_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__5));
v___x_732_ = 0;
v___x_733_ = l_Lean_mkCIdentFrom(v_stx_698_, v___x_731_, v___x_732_);
v___x_734_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___closed__7));
v___x_735_ = l_Lean_mkCIdentFrom(v_stx_698_, v___x_734_, v___x_732_);
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_mk_empty_array_with_capacity(v___x_736_);
v___x_738_ = lean_array_push(v___x_737_, v___x_735_);
v___x_739_ = l_Lean_Syntax_mkApp(v___x_733_, v___x_738_);
v___y_709_ = v___x_739_;
goto v___jp_708_;
}
v___jp_708_:
{
uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_710_ = 1;
v___x_711_ = lean_box(v___x_710_);
v___x_712_ = lean_box(v___x_710_);
lean_inc(v___y_709_);
v___x_713_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_713_, 0, v___y_709_);
lean_closure_set(v___x_713_, 1, v_expectedType_x3f_699_);
lean_closure_set(v___x_713_, 2, v___x_711_);
lean_closure_set(v___x_713_, 3, v___x_712_);
v___x_714_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_698_, v___y_709_, v___x_713_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___boxed(lean_object* v_stx_740_, lean_object* v_expectedType_x3f_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst(v_stx_740_, v_expectedType_x3f_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1(){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_760_ = l_Lean_Elab_Term_termElabAttribute;
v___x_761_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__1));
v___x_762_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___closed__3));
v___x_763_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___boxed), 9, 0);
v___x_764_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_760_, v___x_761_, v___x_762_, v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1___boxed(lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabDirConst__1();
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f(lean_object* v_a_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = lean_box(0);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f___boxed(lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lake_DSL_dummyGetConfig_x3f(v_a_769_);
lean_dec(v_a_769_);
return v_res_770_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_box(0);
v___x_772_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v___x_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg(){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___closed__0);
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg___boxed(lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0(lean_object* v_00_u03b1_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___boxed(lean_object* v_00_u03b1_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0(v_00_u03b1_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_796_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__6));
v___x_812_ = l_String_toRawSubstring_x27(v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l_Lake_DSL_dummyDir___closed__0));
v___x_845_ = l_String_toRawSubstring_x27(v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__36));
v___x_881_ = l_String_toRawSubstring_x27(v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__9));
v___x_895_ = l_String_toRawSubstring_x27(v___x_894_);
return v___x_895_;
}
}
static lean_object* _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__52));
v___x_919_ = l_String_toRawSubstring_x27(v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig(lean_object* v_stx_947_, lean_object* v_expectedType_x3f_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_956_; 
lean_inc(v_expectedType_x3f_948_);
v___x_956_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v___x_957_; uint8_t v___x_958_; lean_object* v_a_960_; 
lean_dec_ref(v___x_956_);
v___x_957_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1));
lean_inc(v_stx_947_);
v___x_958_ = l_Lean_Syntax_isOfKind(v_stx_947_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_965_; 
lean_dec(v_expectedType_x3f_948_);
lean_dec(v_stx_947_);
v___x_965_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig_spec__0___redArg();
return v___x_965_;
}
else
{
lean_object* v___x_966_; lean_object* v_env_967_; lean_object* v___x_968_; lean_object* v_asyncMode_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_966_ = lean_st_ref_get(v_a_954_);
v_env_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc_ref(v_env_967_);
lean_dec(v___x_966_);
v___x_968_ = l_Lake_optsExt;
v_asyncMode_969_ = lean_ctor_get(v___x_968_, 2);
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = l_Lean_Syntax_getArg(v_stx_947_, v___x_970_);
v___x_972_ = lean_box(0);
v___x_973_ = lean_box(0);
v___x_974_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_972_, v___x_968_, v_env_967_, v_asyncMode_969_, v___x_973_);
if (lean_obj_tag(v___x_974_) == 1)
{
lean_object* v_val_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_val_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_val_975_);
lean_dec_ref(v___x_974_);
v___x_976_ = l_Lean_TSyntax_getId(v___x_971_);
lean_dec(v___x_971_);
v___x_977_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_975_, v___x_976_);
lean_dec(v___x_976_);
lean_dec(v_val_975_);
if (lean_obj_tag(v___x_977_) == 1)
{
lean_object* v_val_978_; lean_object* v_ref_979_; lean_object* v_quotContext_980_; lean_object* v_currMacroScope_981_; uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_val_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_val_978_);
lean_dec_ref(v___x_977_);
v_ref_979_ = lean_ctor_get(v_a_953_, 5);
v_quotContext_980_ = lean_ctor_get(v_a_953_, 10);
v_currMacroScope_981_ = lean_ctor_get(v_a_953_, 11);
v___x_982_ = 0;
v___x_983_ = l_Lean_SourceInfo_fromRef(v_ref_979_, v___x_982_);
v___x_984_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5));
v___x_985_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__7);
v___x_986_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__8));
lean_inc(v_currMacroScope_981_);
lean_inc(v_quotContext_980_);
v___x_987_ = l_Lean_addMacroScope(v_quotContext_980_, v___x_986_, v_currMacroScope_981_);
v___x_988_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__12));
lean_inc_n(v___x_983_, 3);
v___x_989_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_989_, 0, v___x_983_);
lean_ctor_set(v___x_989_, 1, v___x_985_);
lean_ctor_set(v___x_989_, 2, v___x_987_);
lean_ctor_set(v___x_989_, 3, v___x_988_);
v___x_990_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14));
v___x_991_ = l_Lean_Syntax_mkStrLit(v_val_978_, v___x_983_);
v___x_992_ = l_Lean_Syntax_node1(v___x_983_, v___x_990_, v___x_991_);
v___x_993_ = l_Lean_Syntax_node2(v___x_983_, v___x_984_, v___x_989_, v___x_992_);
v_a_960_ = v___x_993_;
goto v___jp_959_;
}
else
{
lean_object* v_ref_994_; lean_object* v_quotContext_995_; lean_object* v_currMacroScope_996_; uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_dec(v___x_977_);
v_ref_994_ = lean_ctor_get(v_a_953_, 5);
v_quotContext_995_ = lean_ctor_get(v_a_953_, 10);
v_currMacroScope_996_ = lean_ctor_get(v_a_953_, 11);
v___x_997_ = 0;
v___x_998_ = l_Lean_SourceInfo_fromRef(v_ref_994_, v___x_997_);
v___x_999_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__16));
v___x_1000_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__18));
v___x_1001_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__19));
lean_inc_n(v___x_998_, 12);
v___x_1002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_998_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__21));
v___x_1004_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__22);
lean_inc_n(v_currMacroScope_996_, 4);
lean_inc_n(v_quotContext_995_, 4);
v___x_1005_ = l_Lean_addMacroScope(v_quotContext_995_, v___x_973_, v_currMacroScope_996_);
v___x_1006_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__35));
v___x_1007_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1007_, 0, v___x_998_);
lean_ctor_set(v___x_1007_, 1, v___x_1004_);
lean_ctor_set(v___x_1007_, 2, v___x_1005_);
lean_ctor_set(v___x_1007_, 3, v___x_1006_);
v___x_1008_ = l_Lean_Syntax_node1(v___x_998_, v___x_1003_, v___x_1007_);
v___x_1009_ = l_Lean_Syntax_node2(v___x_998_, v___x_1000_, v___x_1002_, v___x_1008_);
v___x_1010_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__37);
v___x_1011_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__38));
v___x_1012_ = l_Lean_addMacroScope(v_quotContext_995_, v___x_1011_, v_currMacroScope_996_);
v___x_1013_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__41));
v___x_1014_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1014_, 0, v___x_998_);
lean_ctor_set(v___x_1014_, 1, v___x_1010_);
lean_ctor_set(v___x_1014_, 2, v___x_1012_);
lean_ctor_set(v___x_1014_, 3, v___x_1013_);
v___x_1015_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__42));
v___x_1016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_998_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__14));
v___x_1018_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__5));
v___x_1019_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__43);
v___x_1020_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__44));
v___x_1021_ = l_Lean_addMacroScope(v_quotContext_995_, v___x_1020_, v_currMacroScope_996_);
v___x_1022_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__51));
v___x_1023_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1023_, 0, v___x_998_);
lean_ctor_set(v___x_1023_, 1, v___x_1019_);
lean_ctor_set(v___x_1023_, 2, v___x_1021_);
lean_ctor_set(v___x_1023_, 3, v___x_1022_);
v___x_1024_ = lean_obj_once(&l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53, &l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53_once, _init_l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__53);
v___x_1025_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__54));
v___x_1026_ = l_Lean_addMacroScope(v_quotContext_995_, v___x_1025_, v_currMacroScope_996_);
v___x_1027_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__58));
v___x_1028_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1028_, 0, v___x_998_);
lean_ctor_set(v___x_1028_, 1, v___x_1024_);
lean_ctor_set(v___x_1028_, 2, v___x_1026_);
lean_ctor_set(v___x_1028_, 3, v___x_1027_);
v___x_1029_ = l_Lean_Syntax_node1(v___x_998_, v___x_1017_, v___x_1028_);
v___x_1030_ = l_Lean_Syntax_node2(v___x_998_, v___x_1018_, v___x_1023_, v___x_1029_);
v___x_1031_ = l_Lean_Syntax_node1(v___x_998_, v___x_1017_, v___x_1030_);
v___x_1032_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__59));
v___x_1033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_998_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = l_Lean_Syntax_node5(v___x_998_, v___x_999_, v___x_1009_, v___x_1014_, v___x_1016_, v___x_1031_, v___x_1033_);
v_a_960_ = v___x_1034_;
goto v___jp_959_;
}
}
else
{
lean_object* v___x_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___y_1039_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec(v___x_974_);
v___x_1035_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__61));
v___x_1036_ = 0;
v___x_1037_ = l_Lean_mkCIdentFrom(v_stx_947_, v___x_1035_, v___x_1036_);
v___x_1043_ = l_Lean_TSyntax_getId(v___x_971_);
lean_dec(v___x_971_);
v___x_1044_ = lean_box(0);
lean_inc(v___x_1043_);
v___x_1045_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1044_, v___x_1043_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_quoteNameMk(v___x_1043_);
v___y_1039_ = v___x_1046_;
goto v___jp_1038_;
}
else
{
lean_object* v_val_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_dec(v___x_1043_);
v_val_1047_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_val_1047_);
lean_dec_ref(v___x_1045_);
v___x_1048_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__63));
v___x_1049_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__64));
v___x_1050_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__65));
v___x_1051_ = lean_string_intercalate(v___x_1050_, v_val_1047_);
v___x_1052_ = lean_string_append(v___x_1049_, v___x_1051_);
lean_dec_ref(v___x_1051_);
v___x_1053_ = lean_box(2);
v___x_1054_ = l_Lean_Syntax_mkNameLit(v___x_1052_, v___x_1053_);
v___x_1055_ = lean_mk_empty_array_with_capacity(v___x_970_);
v___x_1056_ = lean_array_push(v___x_1055_, v___x_1054_);
v___x_1057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1053_);
lean_ctor_set(v___x_1057_, 1, v___x_1048_);
lean_ctor_set(v___x_1057_, 2, v___x_1056_);
v___y_1039_ = v___x_1057_;
goto v___jp_1038_;
}
v___jp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = lean_mk_empty_array_with_capacity(v___x_970_);
v___x_1041_ = lean_array_push(v___x_1040_, v___y_1039_);
v___x_1042_ = l_Lean_Syntax_mkApp(v___x_1037_, v___x_1041_);
v_a_960_ = v___x_1042_;
goto v___jp_959_;
}
}
}
v___jp_959_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_961_ = lean_box(v___x_958_);
v___x_962_ = lean_box(v___x_958_);
lean_inc(v_a_960_);
v___x_963_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_963_, 0, v_a_960_);
lean_closure_set(v___x_963_, 1, v_expectedType_x3f_948_);
lean_closure_set(v___x_963_, 2, v___x_961_);
lean_closure_set(v___x_963_, 3, v___x_962_);
v___x_964_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lake_DSL_Config_0__Lake_DSL_elabNameConst_spec__0___redArg(v_stx_947_, v_a_960_, v___x_963_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
return v___x_964_;
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec(v_expectedType_x3f_948_);
lean_dec(v_stx_947_);
v_a_1058_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_956_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_956_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
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
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___boxed(lean_object* v_stx_1066_, lean_object* v_expectedType_x3f_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig(v_stx_1066_, v_expectedType_x3f_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1(){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1081_ = l_Lean_Elab_Term_termElabAttribute;
v___x_1082_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___closed__1));
v___x_1083_ = ((lean_object*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___closed__1));
v___x_1084_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___boxed), 9, 0);
v___x_1085_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1081_, v___x_1082_, v___x_1083_, v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1___boxed(lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig___regBuiltin___private_Lake_DSL_Config_0__Lake_DSL_elabGetConfig__1();
return v_res_1087_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Extensions(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Config(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
