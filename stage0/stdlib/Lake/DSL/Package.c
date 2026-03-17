// Lean compiler output
// Module: Lake.DSL.Package
// Imports: public import Lake.DSL.Syntax import Lake.Config.Package import Lake.DSL.Extensions
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lake_DSL_expandAttrs(lean_object*);
extern lean_object* l_Lake_DSL_packageDeclName;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkCApp(lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
extern lean_object* l_Lake_PackageConfig_instConfigInfo;
lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_nameExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lake_Name_quoteFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3_value;
static lean_once_cell_t l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7_value;
static const lean_array_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "where"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "whereStructInst"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_2),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(164, 171, 248, 18, 201, 160, 43, 108)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(175, 253, 70, 178, 90, 186, 195, 40)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed configuration syntax"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23_value;
static lean_once_cell_t l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "declValWhere"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(151, 133, 86, 223, 245, 102, 246, 81)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValStruct"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(133, 214, 189, 204, 150, 4, 239, 13)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structVal"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(111, 76, 221, 200, 37, 245, 130, 150)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_2),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "whereDecls"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_2),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(51, 156, 180, 247, 37, 30, 126, 62)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "\"Use `__name__` instead.\""};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "since"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\"2025-09-18\""};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "nameConst"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(97, 173, 245, 76, 54, 29, 98, 170)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "__name__"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "packageCommand"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value),LEAN_SCALAR_PTR_LITERAL(125, 54, 253, 85, 92, 174, 10, 50)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed package declaration"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "abbrev"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "PackageDecl"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value),LEAN_SCALAR_PTR_LITERAL(225, 4, 178, 81, 27, 213, 197, 136)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value_aux_0),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value),LEAN_SCALAR_PTR_LITERAL(253, 117, 189, 141, 218, 132, 90, 198)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value;
static const lean_array_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "origName"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39_value),LEAN_SCALAR_PTR_LITERAL(60, 90, 152, 77, 27, 27, 68, 80)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_value),LEAN_SCALAR_PTR_LITERAL(207, 146, 87, 28, 198, 178, 209, 199)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 9, .m_data = "«package»"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "package"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_value_aux_0),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56_value),LEAN_SCALAR_PTR_LITERAL(35, 98, 18, 79, 25, 208, 83, 100)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PackageConfig"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value_aux_0),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value),LEAN_SCALAR_PTR_LITERAL(14, 50, 33, 106, 4, 142, 225, 217)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "pkgConfig"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value),LEAN_SCALAR_PTR_LITERAL(84, 166, 20, 31, 6, 123, 63, 83)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1_value),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Package"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 143, 146, 89, 89, 182, 160, 217)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(34, 23, 98, 66, 226, 155, 63, 223)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(178, 95, 147, 209, 102, 192, 116, 165)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(49, 159, 150, 51, 73, 206, 68, 246)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabPackageCommand"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(91, 182, 15, 92, 163, 165, 162, 240)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___boxed(lean_object*);
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "postUpdateDecl"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 217, 106, 51, 176, 161, 152, 100)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "ill-formed post_update declaration"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "postUpdateHook"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(245, 119, 73, 252, 84, 37, 44, 204)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "PostUpdateHookDecl"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(9, 155, 11, 76, 182, 116, 206, 79)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value_aux_0),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(197, 83, 199, 129, 62, 183, 64, 19)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pkg"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12_value),LEAN_SCALAR_PTR_LITERAL(72, 34, 106, 28, 91, 254, 136, 225)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "fn"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15_value),LEAN_SCALAR_PTR_LITERAL(187, 167, 219, 45, 179, 169, 243, 14)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 13, .m_data = "«post_update»"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "post_update"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23_value),LEAN_SCALAR_PTR_LITERAL(27, 22, 136, 29, 51, 248, 173, 13)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "declValDo"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(253, 210, 120, 194, 116, 135, 247, 152)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_2),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_2),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_2),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expandPostUpdateDecl"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 35, 84, 82, 64, 76, 215, 87)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(lean_object* v___y_1_){
_start:
{
lean_object* v___x_3_; lean_object* v_env_4_; lean_object* v___x_5_; lean_object* v_mainModule_6_; lean_object* v___x_7_; 
v___x_3_ = lean_st_ref_get(v___y_1_);
v_env_4_ = lean_ctor_get(v___x_3_, 0);
lean_inc_ref(v_env_4_);
lean_dec(v___x_3_);
v___x_5_ = l_Lean_Environment_header(v_env_4_);
lean_dec_ref(v_env_4_);
v_mainModule_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_mainModule_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v_mainModule_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg___boxed(lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_8_);
lean_dec(v___y_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2(lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___boxed(lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2(v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Elab_Command_getRef___redArg(v___y_19_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_32_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_32_ == 0)
{
v___x_25_ = v___x_22_;
v_isShared_26_ = v_isSharedCheck_32_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_22_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_32_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_30_; 
v___x_27_ = 0;
v___x_28_ = l_Lean_SourceInfo_fromRef(v_a_23_, v___x_27_);
lean_dec(v_a_23_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 0, v___x_28_);
v___x_30_ = v___x_25_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
else
{
lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_40_; 
v_a_33_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_40_ == 0)
{
v___x_35_ = v___x_22_;
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_dec(v___x_22_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_38_; 
if (v_isShared_36_ == 0)
{
v___x_38_ = v___x_35_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_a_33_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0___boxed(lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_44_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_45_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
lean_ctor_set(v___x_50_, 2, v___x_49_);
lean_ctor_set(v___x_50_, 3, v___x_48_);
lean_ctor_set(v___x_50_, 4, v___x_48_);
lean_ctor_set(v___x_50_, 5, v___x_48_);
lean_ctor_set(v___x_50_, 6, v___x_48_);
lean_ctor_set(v___x_50_, 7, v___x_48_);
lean_ctor_set(v___x_50_, 8, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_unsigned_to_nat(32u);
v___x_52_ = lean_mk_empty_array_with_capacity(v___x_51_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_54_ = ((size_t)5ULL);
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_unsigned_to_nat(32u);
v___x_57_ = lean_mk_empty_array_with_capacity(v___x_56_);
v___x_58_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_59_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_55_);
lean_ctor_set(v___x_59_, 3, v___x_55_);
lean_ctor_set_usize(v___x_59_, 4, v___x_54_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_60_ = lean_box(1);
v___x_61_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4);
v___x_62_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_63_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
lean_ctor_set(v___x_63_, 2, v___x_60_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; lean_object* v_env_68_; lean_object* v___x_69_; lean_object* v_scopes_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v_opts_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_67_ = lean_st_ref_get(v___y_65_);
v_env_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_ref(v_env_68_);
lean_dec(v___x_67_);
v___x_69_ = lean_st_ref_get(v___y_65_);
v_scopes_70_ = lean_ctor_get(v___x_69_, 2);
lean_inc(v_scopes_70_);
lean_dec(v___x_69_);
v___x_71_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_72_ = l_List_head_x21___redArg(v___x_71_, v_scopes_70_);
lean_dec(v_scopes_70_);
v_opts_73_ = lean_ctor_get(v___x_72_, 1);
lean_inc_ref(v_opts_73_);
lean_dec(v___x_72_);
v___x_74_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_75_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5);
v___x_76_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_76_, 0, v_env_68_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_75_);
lean_ctor_set(v___x_76_, 3, v_opts_73_);
v___x_77_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v_msgData_64_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msgData_79_, v___y_80_);
lean_dec(v___y_80_);
return v_res_82_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_box(1);
v___x_84_ = l_Lean_MessageData_ofFormat(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2));
v___x_89_ = l_Lean_MessageData_ofFormat(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6(lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
return v_x_90_;
}
else
{
lean_object* v_head_92_; lean_object* v_tail_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_115_; 
v_head_92_ = lean_ctor_get(v_x_91_, 0);
v_tail_93_ = lean_ctor_get(v_x_91_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v_x_91_);
if (v_isSharedCheck_115_ == 0)
{
v___x_95_ = v_x_91_;
v_isShared_96_ = v_isSharedCheck_115_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_tail_93_);
lean_inc(v_head_92_);
lean_dec(v_x_91_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_115_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v_before_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_113_; 
v_before_97_ = lean_ctor_get(v_head_92_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v_head_92_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v_head_92_, 1);
lean_dec(v_unused_114_);
v___x_99_ = v_head_92_;
v_isShared_100_ = v_isSharedCheck_113_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_before_97_);
lean_dec(v_head_92_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_113_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0);
if (v_isShared_100_ == 0)
{
lean_ctor_set_tag(v___x_99_, 7);
lean_ctor_set(v___x_99_, 1, v___x_101_);
lean_ctor_set(v___x_99_, 0, v_x_90_);
v___x_103_ = v___x_99_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_x_90_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_101_);
v___x_103_ = v_reuseFailAlloc_112_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3);
if (v_isShared_96_ == 0)
{
lean_ctor_set_tag(v___x_95_, 7);
lean_ctor_set(v___x_95_, 1, v___x_104_);
lean_ctor_set(v___x_95_, 0, v___x_103_);
v___x_106_ = v___x_95_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v___x_104_);
v___x_106_ = v_reuseFailAlloc_111_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = l_Lean_MessageData_ofSyntax(v_before_97_);
v___x_108_ = l_Lean_indentD(v___x_107_);
v___x_109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_106_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v_x_90_ = v___x_109_;
v_x_91_ = v_tail_93_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(lean_object* v_opts_116_, lean_object* v_opt_117_){
_start:
{
lean_object* v_name_118_; lean_object* v_defValue_119_; lean_object* v_map_120_; lean_object* v___x_121_; 
v_name_118_ = lean_ctor_get(v_opt_117_, 0);
v_defValue_119_ = lean_ctor_get(v_opt_117_, 1);
v_map_120_ = lean_ctor_get(v_opts_116_, 0);
v___x_121_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_120_, v_name_118_);
if (lean_obj_tag(v___x_121_) == 0)
{
uint8_t v___x_122_; 
v___x_122_ = lean_unbox(v_defValue_119_);
return v___x_122_;
}
else
{
lean_object* v_val_123_; 
v_val_123_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_val_123_);
lean_dec_ref(v___x_121_);
if (lean_obj_tag(v_val_123_) == 1)
{
uint8_t v_v_124_; 
v_v_124_ = lean_ctor_get_uint8(v_val_123_, 0);
lean_dec_ref(v_val_123_);
return v_v_124_;
}
else
{
uint8_t v___x_125_; 
lean_dec(v_val_123_);
v___x_125_ = lean_unbox(v_defValue_119_);
return v___x_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5___boxed(lean_object* v_opts_126_, lean_object* v_opt_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(v_opts_126_, v_opt_127_);
lean_dec_ref(v_opt_127_);
lean_dec_ref(v_opts_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_134_ = l_Lean_MessageData_ofFormat(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_135_, lean_object* v_macroStack_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; lean_object* v_scopes_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v_opts_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_139_ = lean_st_ref_get(v___y_137_);
v_scopes_140_ = lean_ctor_get(v___x_139_, 2);
lean_inc(v_scopes_140_);
lean_dec(v___x_139_);
v___x_141_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_142_ = l_List_head_x21___redArg(v___x_141_, v_scopes_140_);
lean_dec(v_scopes_140_);
v_opts_143_ = lean_ctor_get(v___x_142_, 1);
lean_inc_ref(v_opts_143_);
lean_dec(v___x_142_);
v___x_144_ = l_Lean_Elab_pp_macroStack;
v___x_145_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(v_opts_143_, v___x_144_);
lean_dec_ref(v_opts_143_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
lean_dec(v_macroStack_136_);
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v_msgData_135_);
return v___x_146_;
}
else
{
if (lean_obj_tag(v_macroStack_136_) == 0)
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v_msgData_135_);
return v___x_147_;
}
else
{
lean_object* v_head_148_; lean_object* v_after_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_164_; 
v_head_148_ = lean_ctor_get(v_macroStack_136_, 0);
lean_inc(v_head_148_);
v_after_149_ = lean_ctor_get(v_head_148_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_head_148_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; 
v_unused_165_ = lean_ctor_get(v_head_148_, 0);
lean_dec(v_unused_165_);
v___x_151_ = v_head_148_;
v_isShared_152_ = v_isSharedCheck_164_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_after_149_);
lean_dec(v_head_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_164_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0);
if (v_isShared_152_ == 0)
{
lean_ctor_set_tag(v___x_151_, 7);
lean_ctor_set(v___x_151_, 1, v___x_153_);
lean_ctor_set(v___x_151_, 0, v_msgData_135_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_msgData_135_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___x_153_);
v___x_155_ = v_reuseFailAlloc_163_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v_msgData_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_156_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = l_Lean_MessageData_ofSyntax(v_after_149_);
v___x_159_ = l_Lean_indentD(v___x_158_);
v_msgData_160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_160_, 0, v___x_157_);
lean_ctor_set(v_msgData_160_, 1, v___x_159_);
v___x_161_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6(v_msgData_160_, v_macroStack_136_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_166_, lean_object* v_macroStack_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_166_, v_macroStack_167_, v___y_168_);
lean_dec(v___y_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(lean_object* v_msg_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Elab_Command_getRef___redArg(v___y_172_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v_macroStack_177_; lean_object* v___x_178_; lean_object* v_a_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_190_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
lean_dec_ref(v___x_175_);
v_macroStack_177_ = lean_ctor_get(v___y_172_, 4);
lean_inc(v_macroStack_177_);
lean_dec_ref(v___y_172_);
v___x_178_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msg_171_, v___y_173_);
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref(v___x_178_);
lean_inc(v_macroStack_177_);
v___x_180_ = l_Lean_Elab_getBetterRef(v_a_176_, v_macroStack_177_);
lean_dec(v_a_176_);
v___x_181_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_a_179_, v_macroStack_177_, v___y_173_);
v_a_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_190_ == 0)
{
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_180_);
lean_ctor_set(v___x_186_, 1, v_a_182_);
if (v_isShared_185_ == 0)
{
lean_ctor_set_tag(v___x_184_, 1);
lean_ctor_set(v___x_184_, 0, v___x_186_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec_ref(v___y_172_);
lean_dec_ref(v_msg_171_);
v_a_191_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_175_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_175_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg___boxed(lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(lean_object* v_ref_204_, lean_object* v_msg_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Elab_Command_getRef___redArg(v___y_206_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v_fileName_211_; lean_object* v_fileMap_212_; lean_object* v_currRecDepth_213_; lean_object* v_cmdPos_214_; lean_object* v_macroStack_215_; lean_object* v_quotContext_x3f_216_; lean_object* v_currMacroScope_217_; lean_object* v_snap_x3f_218_; lean_object* v_cancelTk_x3f_219_; uint8_t v_suppressElabErrors_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_229_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref(v___x_209_);
v_fileName_211_ = lean_ctor_get(v___y_206_, 0);
v_fileMap_212_ = lean_ctor_get(v___y_206_, 1);
v_currRecDepth_213_ = lean_ctor_get(v___y_206_, 2);
v_cmdPos_214_ = lean_ctor_get(v___y_206_, 3);
v_macroStack_215_ = lean_ctor_get(v___y_206_, 4);
v_quotContext_x3f_216_ = lean_ctor_get(v___y_206_, 5);
v_currMacroScope_217_ = lean_ctor_get(v___y_206_, 6);
v_snap_x3f_218_ = lean_ctor_get(v___y_206_, 8);
v_cancelTk_x3f_219_ = lean_ctor_get(v___y_206_, 9);
v_suppressElabErrors_220_ = lean_ctor_get_uint8(v___y_206_, sizeof(void*)*10);
v_isSharedCheck_229_ = !lean_is_exclusive(v___y_206_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; 
v_unused_230_ = lean_ctor_get(v___y_206_, 7);
lean_dec(v_unused_230_);
v___x_222_ = v___y_206_;
v_isShared_223_ = v_isSharedCheck_229_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_cancelTk_x3f_219_);
lean_inc(v_snap_x3f_218_);
lean_inc(v_currMacroScope_217_);
lean_inc(v_quotContext_x3f_216_);
lean_inc(v_macroStack_215_);
lean_inc(v_cmdPos_214_);
lean_inc(v_currRecDepth_213_);
lean_inc(v_fileMap_212_);
lean_inc(v_fileName_211_);
lean_dec(v___y_206_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_229_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_ref_224_; lean_object* v___x_226_; 
v_ref_224_ = l_Lean_replaceRef(v_ref_204_, v_a_210_);
lean_dec(v_a_210_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 7, v_ref_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_fileName_211_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_fileMap_212_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_currRecDepth_213_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v_cmdPos_214_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v_macroStack_215_);
lean_ctor_set(v_reuseFailAlloc_228_, 5, v_quotContext_x3f_216_);
lean_ctor_set(v_reuseFailAlloc_228_, 6, v_currMacroScope_217_);
lean_ctor_set(v_reuseFailAlloc_228_, 7, v_ref_224_);
lean_ctor_set(v_reuseFailAlloc_228_, 8, v_snap_x3f_218_);
lean_ctor_set(v_reuseFailAlloc_228_, 9, v_cancelTk_x3f_219_);
lean_ctor_set_uint8(v_reuseFailAlloc_228_, sizeof(void*)*10, v_suppressElabErrors_220_);
v___x_226_ = v_reuseFailAlloc_228_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_205_, v___x_226_, v___y_207_);
return v___x_227_;
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec_ref(v___y_206_);
lean_dec_ref(v_msg_205_);
v_a_231_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_209_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_209_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg___boxed(lean_object* v_ref_239_, lean_object* v_msg_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_239_, v_msg_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec(v_ref_239_);
return v_res_244_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4(void){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Array_mkArray0(lean_box(0));
return v___x_250_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23));
v___x_279_ = l_Lean_stringToMessageData(v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(lean_object* v_tyName_307_, lean_object* v_id_308_, lean_object* v_ty_309_, lean_object* v_config_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___x_399_; lean_object* v_whereInfo_401_; lean_object* v_fs_402_; lean_object* v_wds_x3f_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_399_ = l_Lake_PackageConfig_instConfigInfo;
v___x_432_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22));
lean_inc(v_config_310_);
v___x_433_ = l_Lean_Syntax_isOfKind(v_config_310_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v_ty_309_);
lean_dec(v_id_308_);
lean_dec(v_tyName_307_);
v___x_434_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_435_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_310_, v___x_434_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec(v_config_310_);
return v___x_435_;
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = l_Lean_Syntax_getArg(v_config_310_, v___x_436_);
lean_inc(v___x_437_);
v___x_438_ = l_Lean_Syntax_matchesNull(v___x_437_, v___x_436_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_437_);
v___x_440_ = l_Lean_Syntax_matchesNull(v___x_437_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec(v___x_437_);
lean_dec(v_ty_309_);
lean_dec(v_id_308_);
lean_dec(v_tyName_307_);
v___x_441_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_442_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_310_, v___x_441_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec(v_config_310_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_443_ = l_Lean_Syntax_getArg(v___x_437_, v___x_436_);
lean_dec(v___x_437_);
v___x_444_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26));
lean_inc(v___x_443_);
v___x_445_ = l_Lean_Syntax_isOfKind(v___x_443_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28));
lean_inc(v___x_443_);
v___x_447_ = l_Lean_Syntax_isOfKind(v___x_443_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec(v___x_443_);
lean_dec(v_ty_309_);
lean_dec(v_id_308_);
lean_dec(v_tyName_307_);
v___x_448_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_449_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_310_, v___x_448_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec(v_config_310_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_450_ = l_Lean_Syntax_getArg(v___x_443_, v___x_436_);
v___x_451_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30));
lean_inc(v___x_450_);
v___x_452_ = l_Lean_Syntax_isOfKind(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec(v___x_450_);
lean_dec(v___x_443_);
lean_dec(v_ty_309_);
lean_dec(v_id_308_);
lean_dec(v_tyName_307_);
v___x_453_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_454_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_310_, v___x_453_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec(v_config_310_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_455_ = l_Lean_Syntax_getArg(v___x_450_, v___x_439_);
v___x_456_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32));
lean_inc(v___x_455_);
v___x_457_ = l_Lean_Syntax_isOfKind(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v___x_455_);
lean_dec(v___x_450_);
lean_dec(v___x_443_);
lean_dec(v_ty_309_);
lean_dec(v_id_308_);
lean_dec(v_tyName_307_);
v___x_458_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_459_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_310_, v___x_458_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec(v_config_310_);
return v___x_459_;
}
else
{
lean_object* v_tk_460_; lean_object* v___x_461_; lean_object* v_wds_x3f_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_tk_460_ = l_Lean_Syntax_getArg(v___x_450_, v___x_436_);
lean_dec(v___x_450_);
v___x_461_ = l_Lean_Syntax_getArg(v___x_455_, v___x_436_);
lean_dec(v___x_455_);
v___x_469_ = l_Lean_Syntax_getArg(v___x_443_, v___x_439_);
lean_dec(v___x_443_);
v___x_470_ = l_Lean_Syntax_isNone(v___x_469_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
lean_inc(v___x_469_);
v___x_471_ = l_Lean_Syntax_matchesNull(v___x_469_, v___x_439_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec(v___x_469_);
lean_dec(v___x_461_);
lean_dec(v_tk_460_);
lean_dec(v_ty_309_);
lean_dec(v_id_308_);
lean_dec(v_tyName_307_);
v___x_472_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_473_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_310_, v___x_472_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec(v_config_310_);
return v___x_473_;
}
else
{
lean_object* v_wds_x3f_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_wds_x3f_474_ = l_Lean_Syntax_getArg(v___x_469_, v___x_436_);
lean_dec(v___x_469_);
v___x_475_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_474_);
v___x_476_ = l_Lean_Syntax_isOfKind(v_wds_x3f_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_wds_x3f_474_);
lean_dec(v___x_461_);
lean_dec(v_tk_460_);
lean_dec(v_ty_309_);
lean_dec(v_id_308_);
lean_dec(v_tyName_307_);
v___x_477_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_478_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_310_, v___x_477_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec(v_config_310_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v_wds_x3f_474_);
v_wds_x3f_463_ = v___x_479_;
v___y_464_ = v_a_311_;
v___y_465_ = v_a_312_;
goto v___jp_462_;
}
}
}
else
{
lean_object* v___x_480_; 
lean_dec(v___x_469_);
v___x_480_ = lean_box(0);
v_wds_x3f_463_ = v___x_480_;
v___y_464_ = v_a_311_;
v___y_465_ = v_a_312_;
goto v___jp_462_;
}
v___jp_462_:
{
lean_object* v_fs_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_fs_466_ = l_Lean_Syntax_getArgs(v___x_461_);
lean_dec(v___x_461_);
v___x_467_ = l_Lean_Syntax_getHeadInfo(v_tk_460_);
lean_dec(v_tk_460_);
v___x_468_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_466_);
lean_dec_ref(v_fs_466_);
v_whereInfo_401_ = v___x_467_;
v_fs_402_ = v___x_468_;
v_wds_x3f_403_ = v_wds_x3f_463_;
v___y_404_ = v___y_464_;
v___y_405_ = v___y_465_;
goto v___jp_400_;
}
}
}
}
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_481_ = l_Lean_Syntax_getArg(v___x_443_, v___x_439_);
v___x_482_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32));
lean_inc(v___x_481_);
v___x_483_ = l_Lean_Syntax_isOfKind(v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v___x_481_);
lean_dec(v___x_443_);
lean_dec(v_ty_309_);
lean_dec(v_id_308_);
lean_dec(v_tyName_307_);
v___x_484_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_485_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_310_, v___x_484_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec(v_config_310_);
return v___x_485_;
}
else
{
lean_object* v_tk_486_; lean_object* v___x_487_; lean_object* v_wds_x3f_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_tk_486_ = l_Lean_Syntax_getArg(v___x_443_, v___x_436_);
v___x_487_ = l_Lean_Syntax_getArg(v___x_481_, v___x_436_);
lean_dec(v___x_481_);
v___x_495_ = lean_unsigned_to_nat(2u);
v___x_496_ = l_Lean_Syntax_getArg(v___x_443_, v___x_495_);
lean_dec(v___x_443_);
v___x_497_ = l_Lean_Syntax_isNone(v___x_496_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; 
lean_inc(v___x_496_);
v___x_498_ = l_Lean_Syntax_matchesNull(v___x_496_, v___x_439_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec(v___x_496_);
lean_dec(v___x_487_);
lean_dec(v_tk_486_);
lean_dec(v_ty_309_);
lean_dec(v_id_308_);
lean_dec(v_tyName_307_);
v___x_499_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_500_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_310_, v___x_499_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec(v_config_310_);
return v___x_500_;
}
else
{
lean_object* v_wds_x3f_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_wds_x3f_501_ = l_Lean_Syntax_getArg(v___x_496_, v___x_436_);
lean_dec(v___x_496_);
v___x_502_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_501_);
v___x_503_ = l_Lean_Syntax_isOfKind(v_wds_x3f_501_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v_wds_x3f_501_);
lean_dec(v___x_487_);
lean_dec(v_tk_486_);
lean_dec(v_ty_309_);
lean_dec(v_id_308_);
lean_dec(v_tyName_307_);
v___x_504_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_505_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_310_, v___x_504_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec(v_config_310_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; 
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v_wds_x3f_501_);
v_wds_x3f_489_ = v___x_506_;
v___y_490_ = v_a_311_;
v___y_491_ = v_a_312_;
goto v___jp_488_;
}
}
}
else
{
lean_object* v___x_507_; 
lean_dec(v___x_496_);
v___x_507_ = lean_box(0);
v_wds_x3f_489_ = v___x_507_;
v___y_490_ = v_a_311_;
v___y_491_ = v_a_312_;
goto v___jp_488_;
}
v___jp_488_:
{
lean_object* v_fs_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_fs_492_ = l_Lean_Syntax_getArgs(v___x_487_);
lean_dec(v___x_487_);
v___x_493_ = l_Lean_Syntax_getHeadInfo(v_tk_486_);
lean_dec(v_tk_486_);
v___x_494_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_492_);
lean_dec_ref(v_fs_492_);
v_whereInfo_401_ = v___x_493_;
v_fs_402_ = v___x_494_;
v_wds_x3f_403_ = v_wds_x3f_489_;
v___y_404_ = v___y_490_;
v___y_405_ = v___y_491_;
goto v___jp_400_;
}
}
}
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v___x_437_);
v___x_508_ = lean_box(2);
v___x_509_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
v___x_510_ = lean_box(0);
v_whereInfo_401_ = v___x_508_;
v_fs_402_ = v___x_509_;
v_wds_x3f_403_ = v___x_510_;
v___y_404_ = v_a_311_;
v___y_405_ = v_a_312_;
goto v___jp_400_;
}
}
v___jp_314_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_323_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref(v___y_320_);
lean_inc_ref(v___y_319_);
lean_inc_ref(v___y_321_);
v___x_324_ = l_Lean_Name_mkStr4(v___y_321_, v___y_319_, v___y_320_, v___x_323_);
v___x_325_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
lean_inc_ref(v___y_320_);
lean_inc_ref(v___y_319_);
lean_inc_ref(v___y_321_);
v___x_326_ = l_Lean_Name_mkStr4(v___y_321_, v___y_319_, v___y_320_, v___x_325_);
v___x_327_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_328_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc(v___y_315_);
v___x_329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_329_, 0, v___y_315_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
lean_ctor_set(v___x_329_, 2, v___x_328_);
lean_inc_ref_n(v___x_329_, 7);
lean_inc(v___y_315_);
v___x_330_ = l_Lean_Syntax_node7(v___y_315_, v___x_326_, v___x_329_, v___x_329_, v___x_329_, v___x_329_, v___x_329_, v___x_329_, v___x_329_);
v___x_331_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5));
lean_inc_ref(v___y_320_);
lean_inc_ref(v___y_319_);
lean_inc_ref(v___y_321_);
v___x_332_ = l_Lean_Name_mkStr4(v___y_321_, v___y_319_, v___y_320_, v___x_331_);
v___x_333_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6));
lean_inc(v___y_315_);
v___x_334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_334_, 0, v___y_315_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
lean_inc_ref(v___y_320_);
lean_inc_ref(v___y_319_);
lean_inc_ref(v___y_321_);
v___x_336_ = l_Lean_Name_mkStr4(v___y_321_, v___y_319_, v___y_320_, v___x_335_);
v___x_337_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
lean_inc(v___y_317_);
v___x_338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_338_, 0, v___y_317_);
lean_ctor_set(v___x_338_, 1, v___x_327_);
lean_ctor_set(v___x_338_, 2, v___x_337_);
v___x_339_ = lean_unsigned_to_nat(2u);
v___x_340_ = lean_mk_empty_array_with_capacity(v___x_339_);
v___x_341_ = lean_array_push(v___x_340_, v_id_308_);
v___x_342_ = lean_array_push(v___x_341_, v___x_338_);
v___x_343_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_343_, 0, v___y_317_);
lean_ctor_set(v___x_343_, 1, v___x_336_);
lean_ctor_set(v___x_343_, 2, v___x_342_);
v___x_344_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
lean_inc_ref(v___y_319_);
lean_inc_ref(v___y_321_);
v___x_345_ = l_Lean_Name_mkStr4(v___y_321_, v___y_319_, v___y_320_, v___x_344_);
v___x_346_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_347_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_348_ = l_Lean_Name_mkStr4(v___y_321_, v___y_319_, v___x_346_, v___x_347_);
v___x_349_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
lean_inc(v___y_315_);
v___x_350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_350_, 0, v___y_315_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
lean_inc(v___y_315_);
v___x_351_ = l_Lean_Syntax_node2(v___y_315_, v___x_348_, v___x_350_, v_ty_309_);
lean_inc(v___y_315_);
v___x_352_ = l_Lean_Syntax_node1(v___y_315_, v___x_327_, v___x_351_);
lean_inc_ref(v___x_329_);
lean_inc(v___y_315_);
v___x_353_ = l_Lean_Syntax_node2(v___y_315_, v___x_345_, v___x_329_, v___x_352_);
lean_inc(v___y_315_);
v___x_354_ = l_Lean_Syntax_node5(v___y_315_, v___x_332_, v___x_334_, v___x_343_, v___x_353_, v___y_316_, v___x_329_);
v___x_355_ = l_Lean_Syntax_node2(v___y_315_, v___x_324_, v___x_330_, v___x_354_);
lean_inc(v___x_355_);
v___x_356_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_356_, 0, v___x_355_);
v___x_357_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_config_310_, v___x_355_, v___x_356_, v___y_318_, v___y_322_);
return v___x_357_;
}
v___jp_358_:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Elab_Command_getRef___redArg(v___y_361_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_370_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref(v___x_368_);
v___x_370_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_361_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_quotContext_x3f_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; 
lean_dec_ref(v___x_370_);
v_quotContext_x3f_371_ = lean_ctor_get(v___y_361_, 5);
v___x_372_ = l_Lean_mkOptionalNode(v___y_367_);
v___x_373_ = lean_unsigned_to_nat(3u);
v___x_374_ = lean_mk_empty_array_with_capacity(v___x_373_);
v___x_375_ = lean_array_push(v___x_374_, v___y_360_);
v___x_376_ = lean_array_push(v___x_375_, v___y_365_);
v___x_377_ = lean_array_push(v___x_376_, v___x_372_);
v___x_378_ = lean_box(2);
v___x_379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___y_359_);
lean_ctor_set(v___x_379_, 2, v___x_377_);
v___x_380_ = 0;
v___x_381_ = l_Lean_SourceInfo_fromRef(v_a_369_, v___x_380_);
lean_dec(v_a_369_);
if (lean_obj_tag(v_quotContext_x3f_371_) == 0)
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_366_);
lean_dec_ref(v___x_382_);
v___y_315_ = v___x_381_;
v___y_316_ = v___x_379_;
v___y_317_ = v___x_378_;
v___y_318_ = v___y_361_;
v___y_319_ = v___y_362_;
v___y_320_ = v___y_364_;
v___y_321_ = v___y_363_;
v___y_322_ = v___y_366_;
goto v___jp_314_;
}
else
{
v___y_315_ = v___x_381_;
v___y_316_ = v___x_379_;
v___y_317_ = v___x_378_;
v___y_318_ = v___y_361_;
v___y_319_ = v___y_362_;
v___y_320_ = v___y_364_;
v___y_321_ = v___y_363_;
v___y_322_ = v___y_366_;
goto v___jp_314_;
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_a_369_);
lean_dec(v___y_367_);
lean_dec(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec(v___y_359_);
lean_dec(v_config_310_);
lean_dec(v_ty_309_);
lean_dec(v_id_308_);
v_a_383_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_370_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_370_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec(v___y_367_);
lean_dec(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec(v___y_359_);
lean_dec(v_config_310_);
lean_dec(v_ty_309_);
lean_dec(v_id_308_);
v_a_391_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_368_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_368_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
v___jp_400_:
{
lean_object* v_fieldMap_406_; lean_object* v___x_407_; 
v_fieldMap_406_ = lean_ctor_get(v___x_399_, 1);
lean_inc(v_fieldMap_406_);
lean_inc_ref(v___y_404_);
v___x_407_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_307_, v_fieldMap_406_, v_fs_402_, v___y_404_, v___y_405_);
lean_dec_ref(v_fs_402_);
lean_dec(v_fieldMap_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_409_; lean_object* v_whereTk_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref(v___x_407_);
v___x_409_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13));
v_whereTk_410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_whereTk_410_, 0, v_whereInfo_401_);
lean_ctor_set(v_whereTk_410_, 1, v___x_409_);
v___x_411_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_412_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_413_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_414_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18));
if (lean_obj_tag(v_wds_x3f_403_) == 0)
{
lean_object* v___x_415_; 
v___x_415_ = lean_box(0);
v___y_359_ = v___x_414_;
v___y_360_ = v_whereTk_410_;
v___y_361_ = v___y_404_;
v___y_362_ = v___x_412_;
v___y_363_ = v___x_411_;
v___y_364_ = v___x_413_;
v___y_365_ = v_a_408_;
v___y_366_ = v___y_405_;
v___y_367_ = v___x_415_;
goto v___jp_358_;
}
else
{
lean_object* v_val_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
v_val_416_ = lean_ctor_get(v_wds_x3f_403_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_wds_x3f_403_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v_wds_x3f_403_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_val_416_);
lean_dec(v_wds_x3f_403_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_val_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
v___y_359_ = v___x_414_;
v___y_360_ = v_whereTk_410_;
v___y_361_ = v___y_404_;
v___y_362_ = v___x_412_;
v___y_363_ = v___x_411_;
v___y_364_ = v___x_413_;
v___y_365_ = v_a_408_;
v___y_366_ = v___y_405_;
v___y_367_ = v___x_421_;
goto v___jp_358_;
}
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v_wds_x3f_403_);
lean_dec(v_whereInfo_401_);
lean_dec(v_config_310_);
lean_dec(v_ty_309_);
lean_dec(v_id_308_);
v_a_424_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_407_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_407_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___boxed(lean_object* v_tyName_511_, lean_object* v_id_512_, lean_object* v_ty_513_, lean_object* v_config_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v_tyName_511_, v_id_512_, v_ty_513_, v_config_514_, v_a_515_, v_a_516_);
return v_res_518_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13));
v___x_541_ = l_Lean_stringToMessageData(v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19));
v___x_548_ = l_String_toRawSubstring_x27(v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33));
v___x_570_ = l_String_toRawSubstring_x27(v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39));
v___x_578_ = l_String_toRawSubstring_x27(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42));
v___x_583_ = l_String_toRawSubstring_x27(v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49));
v___x_592_ = l_String_toRawSubstring_x27(v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61));
v___x_613_ = l_String_toRawSubstring_x27(v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(lean_object* v_stx_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12));
lean_inc(v_stx_616_);
v___x_689_ = l_Lean_Syntax_isOfKind(v_stx_616_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
v___x_691_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_616_, v___x_690_, v_a_617_, v_a_618_);
lean_dec(v_a_618_);
lean_dec(v_stx_616_);
return v___x_691_;
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; uint8_t v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; uint8_t v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v_a_826_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; uint8_t v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v_a_858_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; uint8_t v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v_a_949_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; uint8_t v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; uint8_t v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v_a_1061_; lean_object* v_kw_1099_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v_nameStx_x3f_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = l_Lean_Syntax_getArg(v_stx_616_, v___x_692_);
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = l_Lean_Syntax_getArg(v_stx_616_, v___x_694_);
v___x_696_ = lean_unsigned_to_nat(2u);
v_kw_1099_ = l_Lean_Syntax_getArg(v_stx_616_, v___x_696_);
v___x_1193_ = lean_unsigned_to_nat(3u);
v___x_1194_ = l_Lean_Syntax_getArg(v_stx_616_, v___x_1193_);
v___x_1195_ = l_Lean_Syntax_isNone(v___x_1194_);
if (v___x_1195_ == 0)
{
uint8_t v___x_1196_; 
lean_inc(v___x_1194_);
v___x_1196_ = l_Lean_Syntax_matchesNull(v___x_1194_, v___x_694_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec(v___x_1194_);
lean_dec(v_kw_1099_);
lean_dec(v___x_695_);
lean_dec(v___x_693_);
v___x_1197_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
v___x_1198_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_616_, v___x_1197_, v_a_617_, v_a_618_);
lean_dec(v_a_618_);
lean_dec(v_stx_616_);
return v___x_1198_;
}
else
{
lean_object* v_nameStx_x3f_1199_; lean_object* v___x_1200_; 
v_nameStx_x3f_1199_ = l_Lean_Syntax_getArg(v___x_1194_, v___x_692_);
lean_dec(v___x_1194_);
v___x_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1200_, 0, v_nameStx_x3f_1199_);
v_nameStx_x3f_1178_ = v___x_1200_;
v___y_1179_ = v_a_617_;
v___y_1180_ = v_a_618_;
goto v___jp_1177_;
}
}
else
{
lean_object* v___x_1201_; 
lean_dec(v___x_1194_);
v___x_1201_ = lean_box(0);
v_nameStx_x3f_1178_ = v___x_1201_;
v___y_1179_ = v_a_617_;
v___y_1180_ = v_a_618_;
goto v___jp_1177_;
}
v___jp_697_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_inc_ref(v___y_721_);
v___x_725_ = l_Array_append___redArg(v___y_721_, v___y_724_);
lean_dec_ref(v___y_724_);
lean_inc(v___y_709_);
lean_inc(v___y_711_);
v___x_726_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_726_, 0, v___y_711_);
lean_ctor_set(v___x_726_, 1, v___y_709_);
lean_ctor_set(v___x_726_, 2, v___x_725_);
v___x_727_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15));
lean_inc_ref(v___y_720_);
lean_inc_ref(v___y_704_);
lean_inc_ref(v___y_717_);
v___x_728_ = l_Lean_Name_mkStr4(v___y_717_, v___y_704_, v___y_720_, v___x_727_);
v___x_729_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16));
lean_inc(v___y_711_);
v___x_730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_730_, 0, v___y_711_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = l_Lean_Syntax_SepArray_ofElems(v___y_705_, v___y_708_);
lean_dec_ref(v___y_708_);
lean_inc_ref(v___y_721_);
v___x_732_ = l_Array_append___redArg(v___y_721_, v___x_731_);
lean_dec_ref(v___x_731_);
lean_inc(v___y_709_);
lean_inc(v___y_711_);
v___x_733_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_733_, 0, v___y_711_);
lean_ctor_set(v___x_733_, 1, v___y_709_);
lean_ctor_set(v___x_733_, 2, v___x_732_);
v___x_734_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17));
lean_inc(v___y_711_);
v___x_735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_735_, 0, v___y_711_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
lean_inc(v___x_728_);
lean_inc(v___y_711_);
v___x_736_ = l_Lean_Syntax_node3(v___y_711_, v___x_728_, v___x_730_, v___x_733_, v___x_735_);
lean_inc(v___y_709_);
lean_inc(v___y_711_);
v___x_737_ = l_Lean_Syntax_node1(v___y_711_, v___y_709_, v___x_736_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_709_);
lean_inc(v___y_711_);
v___x_738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_738_, 0, v___y_711_);
lean_ctor_set(v___x_738_, 1, v___y_709_);
lean_ctor_set(v___x_738_, 2, v___y_721_);
lean_inc_ref_n(v___x_738_, 5);
lean_inc(v___y_700_);
lean_inc(v___y_711_);
v___x_739_ = l_Lean_Syntax_node7(v___y_711_, v___y_700_, v___x_726_, v___x_737_, v___x_738_, v___x_738_, v___x_738_, v___x_738_, v___x_738_);
v___x_740_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18));
lean_inc_ref(v___y_716_);
lean_inc_ref(v___y_704_);
lean_inc_ref(v___y_717_);
v___x_741_ = l_Lean_Name_mkStr4(v___y_717_, v___y_704_, v___y_716_, v___x_740_);
lean_inc(v___y_711_);
v___x_742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_742_, 0, v___y_711_);
lean_ctor_set(v___x_742_, 1, v___x_740_);
v___x_743_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
lean_inc_ref(v___y_716_);
lean_inc_ref(v___y_704_);
lean_inc_ref(v___y_717_);
v___x_744_ = l_Lean_Name_mkStr4(v___y_717_, v___y_704_, v___y_716_, v___x_743_);
v___x_745_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
lean_inc(v___y_709_);
lean_inc(v___y_723_);
v___x_746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_746_, 0, v___y_723_);
lean_ctor_set(v___x_746_, 1, v___y_709_);
lean_ctor_set(v___x_746_, 2, v___x_745_);
v___x_747_ = lean_mk_empty_array_with_capacity(v___x_696_);
lean_inc(v___y_706_);
lean_inc_ref(v___x_747_);
v___x_748_ = lean_array_push(v___x_747_, v___y_706_);
lean_inc_ref(v___x_746_);
v___x_749_ = lean_array_push(v___x_748_, v___x_746_);
lean_inc(v___x_744_);
lean_inc(v___y_723_);
v___x_750_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_750_, 0, v___y_723_);
lean_ctor_set(v___x_750_, 1, v___x_744_);
lean_ctor_set(v___x_750_, 2, v___x_749_);
v___x_751_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
lean_inc_ref(v___y_716_);
lean_inc_ref(v___y_704_);
lean_inc_ref(v___y_717_);
v___x_752_ = l_Lean_Name_mkStr4(v___y_717_, v___y_704_, v___y_716_, v___x_751_);
v___x_753_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
lean_inc_ref(v___y_704_);
lean_inc_ref(v___y_717_);
v___x_754_ = l_Lean_Name_mkStr4(v___y_717_, v___y_704_, v___y_720_, v___x_753_);
v___x_755_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
lean_inc(v___y_711_);
v___x_756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_756_, 0, v___y_711_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20);
v___x_758_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21));
v___x_759_ = l_Lean_addMacroScope(v___y_707_, v___x_758_, v___y_712_);
v___x_760_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23));
v___x_761_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24));
v___x_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v___y_698_);
v___x_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_760_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
lean_inc(v___y_711_);
v___x_764_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_764_, 0, v___y_711_);
lean_ctor_set(v___x_764_, 1, v___x_757_);
lean_ctor_set(v___x_764_, 2, v___x_759_);
lean_ctor_set(v___x_764_, 3, v___x_763_);
lean_inc(v___y_711_);
v___x_765_ = l_Lean_Syntax_node2(v___y_711_, v___x_754_, v___x_756_, v___x_764_);
lean_inc(v___y_709_);
lean_inc(v___y_711_);
v___x_766_ = l_Lean_Syntax_node1(v___y_711_, v___y_709_, v___x_765_);
lean_inc_ref(v___x_738_);
lean_inc(v___x_752_);
lean_inc(v___y_711_);
v___x_767_ = l_Lean_Syntax_node2(v___y_711_, v___x_752_, v___x_738_, v___x_766_);
v___x_768_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25));
lean_inc_ref(v___y_704_);
lean_inc_ref(v___y_717_);
v___x_769_ = l_Lean_Name_mkStr4(v___y_717_, v___y_704_, v___y_716_, v___x_768_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_711_);
v___x_770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_770_, 0, v___y_711_);
lean_ctor_set(v___x_770_, 1, v___y_703_);
v___x_771_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26));
v___x_772_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27));
lean_inc_ref(v___y_717_);
v___x_773_ = l_Lean_Name_mkStr4(v___y_717_, v___y_704_, v___x_771_, v___x_772_);
lean_inc_ref_n(v___x_738_, 2);
lean_inc(v___x_773_);
lean_inc(v___y_711_);
v___x_774_ = l_Lean_Syntax_node2(v___y_711_, v___x_773_, v___x_738_, v___x_738_);
lean_inc(v___x_769_);
lean_inc(v___y_711_);
v___x_775_ = l_Lean_Syntax_node4(v___y_711_, v___x_769_, v___x_770_, v___y_702_, v___x_774_, v___x_738_);
lean_inc(v___x_741_);
lean_inc(v___y_711_);
v___x_776_ = l_Lean_Syntax_node4(v___y_711_, v___x_741_, v___x_742_, v___x_750_, v___x_767_, v___x_775_);
lean_inc(v___y_701_);
v___x_777_ = l_Lean_Syntax_node2(v___y_711_, v___y_701_, v___x_739_, v___x_776_);
lean_inc(v___x_777_);
v___x_778_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_778_, 0, v___x_777_);
lean_inc(v___y_713_);
lean_inc_ref(v___y_714_);
v___x_779_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_stx_616_, v___x_777_, v___x_778_, v___y_714_, v___y_713_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; 
lean_dec_ref(v___x_779_);
v___x_780_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_714_, v___y_713_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_782_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref(v___x_780_);
v___x_782_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_714_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref(v___x_782_);
v___x_783_ = l_Lean_Name_str___override(v___y_699_, v___y_710_);
v___x_784_ = l_Lean_mkIdentFrom(v___y_706_, v___x_783_, v___y_722_);
lean_dec(v___y_706_);
if (lean_obj_tag(v___y_715_) == 0)
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_713_);
lean_dec_ref(v___x_785_);
v___y_621_ = v___x_746_;
v___y_622_ = v___y_700_;
v___y_623_ = v___x_740_;
v___y_624_ = v___y_701_;
v___y_625_ = v___x_734_;
v___y_626_ = v___x_769_;
v___y_627_ = v___x_741_;
v___y_628_ = v___x_773_;
v___y_629_ = v___y_713_;
v___y_630_ = v___y_703_;
v___y_631_ = v___y_714_;
v___y_632_ = v___x_752_;
v___y_633_ = v___y_717_;
v___y_634_ = v___x_728_;
v___y_635_ = v___y_718_;
v___y_636_ = v___y_721_;
v___y_637_ = v___y_719_;
v___y_638_ = v___x_784_;
v___y_639_ = v_a_781_;
v___y_640_ = v___x_747_;
v___y_641_ = v___x_744_;
v___y_642_ = v___y_723_;
v___y_643_ = v___y_709_;
v___y_644_ = v___x_729_;
goto v___jp_620_;
}
else
{
lean_dec_ref(v___y_715_);
v___y_621_ = v___x_746_;
v___y_622_ = v___y_700_;
v___y_623_ = v___x_740_;
v___y_624_ = v___y_701_;
v___y_625_ = v___x_734_;
v___y_626_ = v___x_769_;
v___y_627_ = v___x_741_;
v___y_628_ = v___x_773_;
v___y_629_ = v___y_713_;
v___y_630_ = v___y_703_;
v___y_631_ = v___y_714_;
v___y_632_ = v___x_752_;
v___y_633_ = v___y_717_;
v___y_634_ = v___x_728_;
v___y_635_ = v___y_718_;
v___y_636_ = v___y_721_;
v___y_637_ = v___y_719_;
v___y_638_ = v___x_784_;
v___y_639_ = v_a_781_;
v___y_640_ = v___x_747_;
v___y_641_ = v___x_744_;
v___y_642_ = v___y_723_;
v___y_643_ = v___y_709_;
v___y_644_ = v___x_729_;
goto v___jp_620_;
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v_a_781_);
lean_dec(v___x_773_);
lean_dec(v___x_769_);
lean_dec(v___x_752_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_746_);
lean_dec(v___x_744_);
lean_dec(v___x_741_);
lean_dec(v___x_728_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_701_);
lean_dec(v___y_700_);
lean_dec(v___y_699_);
v_a_786_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_782_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_782_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec(v___x_773_);
lean_dec(v___x_769_);
lean_dec(v___x_752_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_746_);
lean_dec(v___x_744_);
lean_dec(v___x_741_);
lean_dec(v___x_728_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_701_);
lean_dec(v___y_700_);
lean_dec(v___y_699_);
v_a_794_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_780_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_780_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_dec(v___x_773_);
lean_dec(v___x_769_);
lean_dec(v___x_752_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_746_);
lean_dec(v___x_744_);
lean_dec(v___x_741_);
lean_dec(v___x_728_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_701_);
lean_dec(v___y_700_);
lean_dec(v___y_699_);
return v___x_779_;
}
}
v___jp_802_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_827_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_828_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref(v___y_816_);
lean_inc_ref(v___y_814_);
v___x_829_ = l_Lean_Name_mkStr4(v___y_814_, v___y_816_, v___x_827_, v___x_828_);
v___x_830_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
lean_inc_ref(v___y_816_);
lean_inc_ref(v___y_814_);
v___x_831_ = l_Lean_Name_mkStr4(v___y_814_, v___y_816_, v___x_827_, v___x_830_);
if (lean_obj_tag(v___y_806_) == 1)
{
lean_object* v_val_832_; lean_object* v___x_833_; 
v_val_832_ = lean_ctor_get(v___y_806_, 0);
lean_inc(v_val_832_);
lean_dec_ref(v___y_806_);
v___x_833_ = l_Array_mkArray1___redArg(v_val_832_);
v___y_698_ = v___y_803_;
v___y_699_ = v___y_804_;
v___y_700_ = v___x_831_;
v___y_701_ = v___x_829_;
v___y_702_ = v___y_807_;
v___y_703_ = v___y_811_;
v___y_704_ = v___y_816_;
v___y_705_ = v___y_817_;
v___y_706_ = v___y_821_;
v___y_707_ = v_a_826_;
v___y_708_ = v___y_823_;
v___y_709_ = v___y_825_;
v___y_710_ = v___y_805_;
v___y_711_ = v___y_808_;
v___y_712_ = v___y_809_;
v___y_713_ = v___y_810_;
v___y_714_ = v___y_812_;
v___y_715_ = v___y_813_;
v___y_716_ = v___x_827_;
v___y_717_ = v___y_814_;
v___y_718_ = v___y_815_;
v___y_719_ = v___y_820_;
v___y_720_ = v___y_819_;
v___y_721_ = v___y_818_;
v___y_722_ = v___y_822_;
v___y_723_ = v___y_824_;
v___y_724_ = v___x_833_;
goto v___jp_697_;
}
else
{
lean_object* v___x_834_; 
lean_dec(v___y_806_);
v___x_834_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___y_698_ = v___y_803_;
v___y_699_ = v___y_804_;
v___y_700_ = v___x_831_;
v___y_701_ = v___x_829_;
v___y_702_ = v___y_807_;
v___y_703_ = v___y_811_;
v___y_704_ = v___y_816_;
v___y_705_ = v___y_817_;
v___y_706_ = v___y_821_;
v___y_707_ = v_a_826_;
v___y_708_ = v___y_823_;
v___y_709_ = v___y_825_;
v___y_710_ = v___y_805_;
v___y_711_ = v___y_808_;
v___y_712_ = v___y_809_;
v___y_713_ = v___y_810_;
v___y_714_ = v___y_812_;
v___y_715_ = v___y_813_;
v___y_716_ = v___x_827_;
v___y_717_ = v___y_814_;
v___y_718_ = v___y_815_;
v___y_719_ = v___y_820_;
v___y_720_ = v___y_819_;
v___y_721_ = v___y_818_;
v___y_722_ = v___y_822_;
v___y_723_ = v___y_824_;
v___y_724_ = v___x_834_;
goto v___jp_697_;
}
}
v___jp_835_:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_859_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
lean_inc_ref(v___y_848_);
lean_inc_ref(v___y_846_);
lean_inc_ref(v___y_843_);
v___x_860_ = l_Lean_Name_mkStr4(v___y_843_, v___y_846_, v___y_848_, v___x_859_);
v___x_861_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
lean_inc(v___y_849_);
v___x_862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_862_, 0, v___y_849_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
lean_inc_ref(v___y_850_);
lean_inc(v___y_857_);
lean_inc(v___y_849_);
v___x_863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_863_, 0, v___y_849_);
lean_ctor_set(v___x_863_, 1, v___y_857_);
lean_ctor_set(v___x_863_, 2, v___y_850_);
v___x_864_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31));
lean_inc_ref(v___y_848_);
lean_inc_ref(v___y_846_);
lean_inc_ref(v___y_843_);
v___x_865_ = l_Lean_Name_mkStr4(v___y_843_, v___y_846_, v___y_848_, v___x_864_);
v___x_866_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31));
lean_inc_ref(v___y_848_);
lean_inc_ref(v___y_846_);
lean_inc_ref(v___y_843_);
v___x_867_ = l_Lean_Name_mkStr4(v___y_843_, v___y_846_, v___y_848_, v___x_866_);
v___x_868_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32));
lean_inc_ref(v___y_848_);
lean_inc_ref(v___y_846_);
lean_inc_ref(v___y_843_);
v___x_869_ = l_Lean_Name_mkStr4(v___y_843_, v___y_846_, v___y_848_, v___x_868_);
v___x_870_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33));
v___x_871_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34);
v___x_872_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35));
lean_inc(v___y_836_);
lean_inc(v_a_858_);
v___x_873_ = l_Lean_addMacroScope(v_a_858_, v___x_872_, v___y_836_);
lean_inc(v___y_838_);
lean_inc(v___y_849_);
v___x_874_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_874_, 0, v___y_849_);
lean_ctor_set(v___x_874_, 1, v___x_871_);
lean_ctor_set(v___x_874_, 2, v___x_873_);
lean_ctor_set(v___x_874_, 3, v___y_838_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_869_);
lean_inc(v___y_849_);
v___x_875_ = l_Lean_Syntax_node2(v___y_849_, v___x_869_, v___x_874_, v___x_863_);
v___x_876_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36));
lean_inc_ref(v___y_848_);
lean_inc_ref(v___y_846_);
lean_inc_ref(v___y_843_);
v___x_877_ = l_Lean_Name_mkStr4(v___y_843_, v___y_846_, v___y_848_, v___x_876_);
v___x_878_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37));
lean_inc(v___y_849_);
v___x_879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_879_, 0, v___y_849_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
lean_inc_ref(v___x_863_);
lean_inc_ref(v___x_879_);
lean_inc(v___x_877_);
lean_inc(v___y_849_);
v___x_880_ = l_Lean_Syntax_node3(v___y_849_, v___x_877_, v___x_879_, v___x_863_, v___y_845_);
lean_inc_ref_n(v___x_863_, 2);
lean_inc(v___y_857_);
lean_inc(v___y_849_);
v___x_881_ = l_Lean_Syntax_node3(v___y_849_, v___y_857_, v___x_863_, v___x_863_, v___x_880_);
lean_inc(v___x_867_);
lean_inc(v___y_849_);
v___x_882_ = l_Lean_Syntax_node2(v___y_849_, v___x_867_, v___x_875_, v___x_881_);
v___x_883_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38));
lean_inc(v___y_849_);
v___x_884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_884_, 0, v___y_849_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40);
v___x_886_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41));
lean_inc(v___y_836_);
lean_inc(v_a_858_);
v___x_887_ = l_Lean_addMacroScope(v_a_858_, v___x_886_, v___y_836_);
lean_inc(v___y_838_);
lean_inc(v___y_849_);
v___x_888_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_888_, 0, v___y_849_);
lean_ctor_set(v___x_888_, 1, v___x_885_);
lean_ctor_set(v___x_888_, 2, v___x_887_);
lean_ctor_set(v___x_888_, 3, v___y_838_);
lean_inc_ref(v___x_863_);
lean_inc(v___x_869_);
lean_inc(v___y_849_);
v___x_889_ = l_Lean_Syntax_node2(v___y_849_, v___x_869_, v___x_888_, v___x_863_);
lean_inc_ref(v___x_863_);
lean_inc_ref(v___x_879_);
lean_inc(v___x_877_);
lean_inc(v___y_849_);
v___x_890_ = l_Lean_Syntax_node3(v___y_849_, v___x_877_, v___x_879_, v___x_863_, v___y_851_);
lean_inc_ref_n(v___x_863_, 2);
lean_inc(v___y_857_);
lean_inc(v___y_849_);
v___x_891_ = l_Lean_Syntax_node3(v___y_849_, v___y_857_, v___x_863_, v___x_863_, v___x_890_);
lean_inc(v___x_867_);
lean_inc(v___y_849_);
v___x_892_ = l_Lean_Syntax_node2(v___y_849_, v___x_867_, v___x_889_, v___x_891_);
v___x_893_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43);
v___x_894_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44));
v___x_895_ = l_Lean_addMacroScope(v_a_858_, v___x_894_, v___y_836_);
lean_inc(v___y_838_);
lean_inc(v___y_849_);
v___x_896_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_896_, 0, v___y_849_);
lean_ctor_set(v___x_896_, 1, v___x_893_);
lean_ctor_set(v___x_896_, 2, v___x_895_);
lean_ctor_set(v___x_896_, 3, v___y_838_);
lean_inc_ref(v___x_863_);
lean_inc(v___y_849_);
v___x_897_ = l_Lean_Syntax_node2(v___y_849_, v___x_869_, v___x_896_, v___x_863_);
lean_inc_ref(v___x_863_);
lean_inc(v___y_849_);
v___x_898_ = l_Lean_Syntax_node3(v___y_849_, v___x_877_, v___x_879_, v___x_863_, v___y_856_);
lean_inc_ref_n(v___x_863_, 2);
lean_inc(v___y_857_);
lean_inc(v___y_849_);
v___x_899_ = l_Lean_Syntax_node3(v___y_849_, v___y_857_, v___x_863_, v___x_863_, v___x_898_);
lean_inc(v___y_849_);
v___x_900_ = l_Lean_Syntax_node2(v___y_849_, v___x_867_, v___x_897_, v___x_899_);
lean_inc_ref(v___x_884_);
lean_inc(v___y_857_);
lean_inc(v___y_849_);
v___x_901_ = l_Lean_Syntax_node5(v___y_849_, v___y_857_, v___x_882_, v___x_884_, v___x_892_, v___x_884_, v___x_900_);
lean_inc(v___y_849_);
v___x_902_ = l_Lean_Syntax_node1(v___y_849_, v___x_865_, v___x_901_);
v___x_903_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45));
lean_inc_ref(v___y_848_);
lean_inc_ref(v___y_846_);
lean_inc_ref(v___y_843_);
v___x_904_ = l_Lean_Name_mkStr4(v___y_843_, v___y_846_, v___y_848_, v___x_903_);
lean_inc_ref(v___x_863_);
lean_inc(v___y_849_);
v___x_905_ = l_Lean_Syntax_node1(v___y_849_, v___x_904_, v___x_863_);
v___x_906_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46));
lean_inc(v___y_849_);
v___x_907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_907_, 0, v___y_849_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
lean_inc_ref(v___x_863_);
v___x_908_ = l_Lean_Syntax_node6(v___y_849_, v___x_860_, v___x_862_, v___x_863_, v___x_902_, v___x_905_, v___x_863_, v___x_907_);
v___x_909_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_841_, v___y_840_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_911_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref(v___x_909_);
v___x_911_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_841_);
if (lean_obj_tag(v___x_911_) == 0)
{
if (lean_obj_tag(v___y_842_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v_a_914_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref(v___x_911_);
v___x_913_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_840_);
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v___x_913_);
v___y_803_ = v___y_838_;
v___y_804_ = v___y_837_;
v___y_805_ = v___x_870_;
v___y_806_ = v___y_839_;
v___y_807_ = v___x_908_;
v___y_808_ = v_a_910_;
v___y_809_ = v_a_912_;
v___y_810_ = v___y_840_;
v___y_811_ = v___x_878_;
v___y_812_ = v___y_841_;
v___y_813_ = v___y_842_;
v___y_814_ = v___y_843_;
v___y_815_ = v___y_844_;
v___y_816_ = v___y_846_;
v___y_817_ = v___x_883_;
v___y_818_ = v___y_850_;
v___y_819_ = v___y_848_;
v___y_820_ = v___y_847_;
v___y_821_ = v___y_852_;
v___y_822_ = v___y_854_;
v___y_823_ = v___y_853_;
v___y_824_ = v___y_855_;
v___y_825_ = v___y_857_;
v_a_826_ = v_a_914_;
goto v___jp_802_;
}
else
{
lean_object* v_a_915_; lean_object* v_val_916_; 
v_a_915_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_915_);
lean_dec_ref(v___x_911_);
v_val_916_ = lean_ctor_get(v___y_842_, 0);
lean_inc(v_val_916_);
v___y_803_ = v___y_838_;
v___y_804_ = v___y_837_;
v___y_805_ = v___x_870_;
v___y_806_ = v___y_839_;
v___y_807_ = v___x_908_;
v___y_808_ = v_a_910_;
v___y_809_ = v_a_915_;
v___y_810_ = v___y_840_;
v___y_811_ = v___x_878_;
v___y_812_ = v___y_841_;
v___y_813_ = v___y_842_;
v___y_814_ = v___y_843_;
v___y_815_ = v___y_844_;
v___y_816_ = v___y_846_;
v___y_817_ = v___x_883_;
v___y_818_ = v___y_850_;
v___y_819_ = v___y_848_;
v___y_820_ = v___y_847_;
v___y_821_ = v___y_852_;
v___y_822_ = v___y_854_;
v___y_823_ = v___y_853_;
v___y_824_ = v___y_855_;
v___y_825_ = v___y_857_;
v_a_826_ = v_val_916_;
goto v___jp_802_;
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_a_910_);
lean_dec(v___x_908_);
lean_dec(v___y_857_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_850_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec(v___y_839_);
lean_dec(v___y_838_);
lean_dec(v___y_837_);
lean_dec(v_stx_616_);
v_a_917_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_911_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_911_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v___x_908_);
lean_dec(v___y_857_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_850_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec(v___y_839_);
lean_dec(v___y_838_);
lean_dec(v___y_837_);
lean_dec(v_stx_616_);
v_a_925_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_909_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_909_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
v___jp_933_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_950_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_951_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_952_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47));
lean_inc_ref(v___y_942_);
v___x_953_ = l_Lean_Name_mkStr4(v___y_942_, v___x_950_, v___x_951_, v___x_952_);
v___x_954_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48));
lean_inc_ref(v___y_942_);
v___x_955_ = l_Lean_Name_mkStr4(v___y_942_, v___x_950_, v___x_951_, v___x_954_);
v___x_956_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_957_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc(v___y_941_);
v___x_958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_958_, 0, v___y_941_);
lean_ctor_set(v___x_958_, 1, v___x_956_);
lean_ctor_set(v___x_958_, 2, v___x_957_);
lean_inc_ref(v___x_958_);
lean_inc(v___x_955_);
lean_inc(v___y_941_);
v___x_959_ = l_Lean_Syntax_node1(v___y_941_, v___x_955_, v___x_958_);
v___x_960_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_940_, v___y_939_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref(v___x_960_);
v___x_962_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_940_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref(v___x_962_);
v___x_964_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50);
v___x_965_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52));
v___x_966_ = l_Lean_addMacroScope(v_a_949_, v___x_965_, v___y_938_);
lean_inc(v___y_935_);
lean_inc(v___y_941_);
v___x_967_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_967_, 0, v___y_941_);
lean_ctor_set(v___x_967_, 1, v___x_964_);
lean_ctor_set(v___x_967_, 2, v___x_966_);
lean_ctor_set(v___x_967_, 3, v___y_935_);
v___x_968_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53));
v___x_969_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54));
lean_inc_ref(v___y_942_);
v___x_970_ = l_Lean_Name_mkStr4(v___y_942_, v___x_950_, v___x_968_, v___x_969_);
lean_inc(v___y_941_);
v___x_971_ = l_Lean_Syntax_node2(v___y_941_, v___x_970_, v___x_967_, v___x_958_);
lean_inc(v___x_953_);
v___x_972_ = l_Lean_Syntax_node2(v___y_941_, v___x_953_, v___x_959_, v___x_971_);
v___x_973_ = lean_mk_empty_array_with_capacity(v___x_694_);
v___x_974_ = lean_array_push(v___x_973_, v___x_972_);
v___x_975_ = l_Lake_DSL_expandAttrs(v___y_934_);
v___x_976_ = l_Array_append___redArg(v___x_974_, v___x_975_);
lean_dec_ref(v___x_975_);
v___x_977_ = l_Lake_DSL_packageDeclName;
v___x_978_ = l_Lean_mkIdentFrom(v___y_936_, v___x_977_, v___y_946_);
lean_dec(v___y_936_);
if (lean_obj_tag(v___y_943_) == 0)
{
lean_object* v___x_979_; lean_object* v_a_980_; 
v___x_979_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_939_);
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref(v___x_979_);
v___y_836_ = v_a_963_;
v___y_837_ = v___x_977_;
v___y_838_ = v___y_935_;
v___y_839_ = v___y_937_;
v___y_840_ = v___y_939_;
v___y_841_ = v___y_940_;
v___y_842_ = v___y_943_;
v___y_843_ = v___y_942_;
v___y_844_ = v___x_953_;
v___y_845_ = v___y_944_;
v___y_846_ = v___x_950_;
v___y_847_ = v___x_955_;
v___y_848_ = v___x_951_;
v___y_849_ = v_a_961_;
v___y_850_ = v___x_957_;
v___y_851_ = v___y_945_;
v___y_852_ = v___x_978_;
v___y_853_ = v___x_976_;
v___y_854_ = v___y_946_;
v___y_855_ = v___y_948_;
v___y_856_ = v___y_947_;
v___y_857_ = v___x_956_;
v_a_858_ = v_a_980_;
goto v___jp_835_;
}
else
{
lean_object* v_val_981_; 
v_val_981_ = lean_ctor_get(v___y_943_, 0);
lean_inc(v_val_981_);
v___y_836_ = v_a_963_;
v___y_837_ = v___x_977_;
v___y_838_ = v___y_935_;
v___y_839_ = v___y_937_;
v___y_840_ = v___y_939_;
v___y_841_ = v___y_940_;
v___y_842_ = v___y_943_;
v___y_843_ = v___y_942_;
v___y_844_ = v___x_953_;
v___y_845_ = v___y_944_;
v___y_846_ = v___x_950_;
v___y_847_ = v___x_955_;
v___y_848_ = v___x_951_;
v___y_849_ = v_a_961_;
v___y_850_ = v___x_957_;
v___y_851_ = v___y_945_;
v___y_852_ = v___x_978_;
v___y_853_ = v___x_976_;
v___y_854_ = v___y_946_;
v___y_855_ = v___y_948_;
v___y_856_ = v___y_947_;
v___y_857_ = v___x_956_;
v_a_858_ = v_val_981_;
goto v___jp_835_;
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec(v_a_961_);
lean_dec(v___x_959_);
lean_dec_ref(v___x_958_);
lean_dec(v___x_955_);
lean_dec(v___x_953_);
lean_dec(v_a_949_);
lean_dec(v___y_948_);
lean_dec(v___y_947_);
lean_dec(v___y_945_);
lean_dec(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v___y_935_);
lean_dec(v___y_934_);
lean_dec(v_stx_616_);
v_a_982_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_962_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_962_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v___x_959_);
lean_dec_ref(v___x_958_);
lean_dec(v___x_955_);
lean_dec(v___x_953_);
lean_dec(v_a_949_);
lean_dec(v___y_948_);
lean_dec(v___y_947_);
lean_dec(v___y_945_);
lean_dec(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v___y_935_);
lean_dec(v___y_934_);
lean_dec(v_stx_616_);
v_a_990_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_960_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_960_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
v___jp_998_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1012_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1013_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57));
v___x_1014_ = l_Nat_reprFast(v___y_1003_);
v___x_1015_ = lean_box(2);
v___x_1016_ = l_Lean_Syntax_mkNumLit(v___x_1014_, v___x_1015_);
v___x_1017_ = lean_mk_empty_array_with_capacity(v___x_696_);
lean_inc_ref(v___x_1017_);
v___x_1018_ = lean_array_push(v___x_1017_, v___y_1011_);
v___x_1019_ = lean_array_push(v___x_1018_, v___x_1016_);
v___x_1020_ = l_Lean_Syntax_mkCApp(v___x_1013_, v___x_1019_);
v___x_1021_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59));
lean_inc(v___x_1020_);
v___x_1022_ = lean_array_push(v___x_1017_, v___x_1020_);
lean_inc(v___y_1007_);
v___x_1023_ = lean_array_push(v___x_1022_, v___y_1007_);
v___x_1024_ = l_Lean_Syntax_mkCApp(v___x_1021_, v___x_1023_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1009_);
v___x_1025_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v___x_1021_, v___y_1009_, v___x_1024_, v___y_1010_, v___y_1005_, v___y_1004_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v___x_1026_; 
lean_dec_ref(v___x_1025_);
v___x_1026_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_1005_, v___y_1004_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1005_);
if (lean_obj_tag(v___x_1028_) == 0)
{
if (lean_obj_tag(v___y_1006_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1030_; lean_object* v_a_1031_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1004_);
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref(v___x_1030_);
v___y_934_ = v___y_999_;
v___y_935_ = v___y_1000_;
v___y_936_ = v___y_1001_;
v___y_937_ = v___y_1002_;
v___y_938_ = v_a_1029_;
v___y_939_ = v___y_1004_;
v___y_940_ = v___y_1005_;
v___y_941_ = v_a_1027_;
v___y_942_ = v___x_1012_;
v___y_943_ = v___y_1006_;
v___y_944_ = v___x_1020_;
v___y_945_ = v___y_1007_;
v___y_946_ = v___y_1008_;
v___y_947_ = v___y_1009_;
v___y_948_ = v___x_1015_;
v_a_949_ = v_a_1031_;
goto v___jp_933_;
}
else
{
lean_object* v_a_1032_; lean_object* v_val_1033_; 
v_a_1032_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1032_);
lean_dec_ref(v___x_1028_);
v_val_1033_ = lean_ctor_get(v___y_1006_, 0);
lean_inc(v_val_1033_);
v___y_934_ = v___y_999_;
v___y_935_ = v___y_1000_;
v___y_936_ = v___y_1001_;
v___y_937_ = v___y_1002_;
v___y_938_ = v_a_1032_;
v___y_939_ = v___y_1004_;
v___y_940_ = v___y_1005_;
v___y_941_ = v_a_1027_;
v___y_942_ = v___x_1012_;
v___y_943_ = v___y_1006_;
v___y_944_ = v___x_1020_;
v___y_945_ = v___y_1007_;
v___y_946_ = v___y_1008_;
v___y_947_ = v___y_1009_;
v___y_948_ = v___x_1015_;
v_a_949_ = v_val_1033_;
goto v___jp_933_;
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v_a_1027_);
lean_dec(v___x_1020_);
lean_dec(v___y_1009_);
lean_dec(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec(v___y_999_);
lean_dec(v_stx_616_);
v_a_1034_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1028_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1028_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v___x_1020_);
lean_dec(v___y_1009_);
lean_dec(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec(v___y_999_);
lean_dec(v_stx_616_);
v_a_1042_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1026_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1026_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_dec(v___x_1020_);
lean_dec(v___y_1009_);
lean_dec(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec(v___y_999_);
lean_dec(v_stx_616_);
return v___x_1025_;
}
}
v___jp_1050_:
{
lean_object* v___x_1062_; 
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1059_);
v___x_1062_ = l_Lake_DSL_mkConfigDeclIdent(v___y_1053_, v___y_1059_, v___y_1058_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v_env_1065_; lean_object* v___x_1066_; lean_object* v_asyncMode_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1086_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref(v___x_1062_);
v___x_1064_ = lean_st_ref_get(v___y_1058_);
v_env_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc_ref(v_env_1065_);
lean_dec(v___x_1064_);
v___x_1066_ = l_Lake_nameExt;
v_asyncMode_1067_ = lean_ctor_get(v___x_1066_, 2);
lean_inc(v_asyncMode_1067_);
v___x_1068_ = lean_box(0);
v___x_1069_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60));
v___x_1070_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1069_, v___x_1066_, v_env_1065_, v_asyncMode_1067_, v___x_1068_);
lean_dec(v_asyncMode_1067_);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; lean_object* v_unused_1088_; lean_object* v_unused_1089_; lean_object* v_unused_1090_; 
v_unused_1087_ = lean_ctor_get(v___x_1066_, 3);
lean_dec(v_unused_1087_);
v_unused_1088_ = lean_ctor_get(v___x_1066_, 2);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v___x_1066_, 1);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v___x_1066_, 0);
lean_dec(v_unused_1090_);
v___x_1072_ = v___x_1066_;
v_isShared_1073_ = v_isSharedCheck_1086_;
goto v_resetjp_1071_;
}
else
{
lean_dec(v___x_1066_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1086_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v_fst_1074_; lean_object* v_snd_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v_fst_1074_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_fst_1074_);
v_snd_1075_ = lean_ctor_get(v___x_1070_, 1);
lean_inc(v_snd_1075_);
lean_dec(v___x_1070_);
v___x_1076_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62);
v___x_1077_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63));
v___x_1078_ = l_Lean_addMacroScope(v_a_1061_, v___x_1077_, v___y_1052_);
v___x_1079_ = lean_box(0);
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 3);
lean_ctor_set(v___x_1072_, 3, v___x_1079_);
lean_ctor_set(v___x_1072_, 2, v___x_1078_);
lean_ctor_set(v___x_1072_, 1, v___x_1076_);
lean_ctor_set(v___x_1072_, 0, v___y_1055_);
v___x_1081_ = v___x_1072_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___y_1055_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = l_Lean_TSyntax_getId(v_a_1063_);
lean_inc(v_a_1063_);
v___x_1083_ = l_Lake_Name_quoteFrom(v_a_1063_, v___x_1082_, v___y_1056_);
if (lean_obj_tag(v_snd_1075_) == 0)
{
lean_inc(v___x_1083_);
v___y_999_ = v___y_1051_;
v___y_1000_ = v___x_1079_;
v___y_1001_ = v_a_1063_;
v___y_1002_ = v___y_1054_;
v___y_1003_ = v_fst_1074_;
v___y_1004_ = v___y_1058_;
v___y_1005_ = v___y_1059_;
v___y_1006_ = v___y_1060_;
v___y_1007_ = v___x_1083_;
v___y_1008_ = v___y_1056_;
v___y_1009_ = v___x_1081_;
v___y_1010_ = v___y_1057_;
v___y_1011_ = v___x_1083_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1084_; 
lean_inc(v_a_1063_);
v___x_1084_ = l_Lake_Name_quoteFrom(v_a_1063_, v_snd_1075_, v___y_1056_);
v___y_999_ = v___y_1051_;
v___y_1000_ = v___x_1079_;
v___y_1001_ = v_a_1063_;
v___y_1002_ = v___y_1054_;
v___y_1003_ = v_fst_1074_;
v___y_1004_ = v___y_1058_;
v___y_1005_ = v___y_1059_;
v___y_1006_ = v___y_1060_;
v___y_1007_ = v___x_1083_;
v___y_1008_ = v___y_1056_;
v___y_1009_ = v___x_1081_;
v___y_1010_ = v___y_1057_;
v___y_1011_ = v___x_1084_;
goto v___jp_998_;
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v_a_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec(v_stx_616_);
v_a_1091_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1062_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1062_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
v___jp_1100_:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_Elab_Command_getRef___redArg(v___y_1105_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v_fileName_1109_; lean_object* v_fileMap_1110_; lean_object* v_currRecDepth_1111_; lean_object* v_cmdPos_1112_; lean_object* v_macroStack_1113_; lean_object* v_quotContext_x3f_1114_; lean_object* v_currMacroScope_1115_; lean_object* v_snap_x3f_1116_; lean_object* v_cancelTk_x3f_1117_; uint8_t v_suppressElabErrors_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1151_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref(v___x_1107_);
v_fileName_1109_ = lean_ctor_get(v___y_1105_, 0);
v_fileMap_1110_ = lean_ctor_get(v___y_1105_, 1);
v_currRecDepth_1111_ = lean_ctor_get(v___y_1105_, 2);
v_cmdPos_1112_ = lean_ctor_get(v___y_1105_, 3);
v_macroStack_1113_ = lean_ctor_get(v___y_1105_, 4);
v_quotContext_x3f_1114_ = lean_ctor_get(v___y_1105_, 5);
v_currMacroScope_1115_ = lean_ctor_get(v___y_1105_, 6);
v_snap_x3f_1116_ = lean_ctor_get(v___y_1105_, 8);
v_cancelTk_x3f_1117_ = lean_ctor_get(v___y_1105_, 9);
v_suppressElabErrors_1118_ = lean_ctor_get_uint8(v___y_1105_, sizeof(void*)*10);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___y_1105_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v___y_1105_, 7);
lean_dec(v_unused_1152_);
v___x_1120_ = v___y_1105_;
v_isShared_1121_ = v_isSharedCheck_1151_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_cancelTk_x3f_1117_);
lean_inc(v_snap_x3f_1116_);
lean_inc(v_currMacroScope_1115_);
lean_inc(v_quotContext_x3f_1114_);
lean_inc(v_macroStack_1113_);
lean_inc(v_cmdPos_1112_);
lean_inc(v_currRecDepth_1111_);
lean_inc(v_fileMap_1110_);
lean_inc(v_fileName_1109_);
lean_dec(v___y_1105_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1151_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v_ref_1122_; lean_object* v___x_1124_; 
v_ref_1122_ = l_Lean_replaceRef(v_kw_1099_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec(v_kw_1099_);
lean_inc(v_quotContext_x3f_1114_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 7, v_ref_1122_);
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_fileName_1109_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_fileMap_1110_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_currRecDepth_1111_);
lean_ctor_set(v_reuseFailAlloc_1150_, 3, v_cmdPos_1112_);
lean_ctor_set(v_reuseFailAlloc_1150_, 4, v_macroStack_1113_);
lean_ctor_set(v_reuseFailAlloc_1150_, 5, v_quotContext_x3f_1114_);
lean_ctor_set(v_reuseFailAlloc_1150_, 6, v_currMacroScope_1115_);
lean_ctor_set(v_reuseFailAlloc_1150_, 7, v_ref_1122_);
lean_ctor_set(v_reuseFailAlloc_1150_, 8, v_snap_x3f_1116_);
lean_ctor_set(v_reuseFailAlloc_1150_, 9, v_cancelTk_x3f_1117_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, sizeof(void*)*10, v_suppressElabErrors_1118_);
v___x_1124_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_Elab_Command_getRef___redArg(v___x_1124_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1127_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref(v___x_1125_);
v___x_1127_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1124_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; uint8_t v___x_1129_; lean_object* v___x_1130_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref(v___x_1127_);
v___x_1129_ = 0;
v___x_1130_ = l_Lean_SourceInfo_fromRef(v_a_1126_, v___x_1129_);
lean_dec(v_a_1126_);
if (lean_obj_tag(v_quotContext_x3f_1114_) == 0)
{
lean_object* v___x_1131_; lean_object* v_a_1132_; 
v___x_1131_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1104_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref(v___x_1131_);
v___y_1051_ = v___y_1101_;
v___y_1052_ = v_a_1128_;
v___y_1053_ = v___y_1102_;
v___y_1054_ = v___y_1106_;
v___y_1055_ = v___x_1130_;
v___y_1056_ = v___x_1129_;
v___y_1057_ = v___y_1103_;
v___y_1058_ = v___y_1104_;
v___y_1059_ = v___x_1124_;
v___y_1060_ = v_quotContext_x3f_1114_;
v_a_1061_ = v_a_1132_;
goto v___jp_1050_;
}
else
{
lean_object* v_val_1133_; 
v_val_1133_ = lean_ctor_get(v_quotContext_x3f_1114_, 0);
lean_inc(v_val_1133_);
v___y_1051_ = v___y_1101_;
v___y_1052_ = v_a_1128_;
v___y_1053_ = v___y_1102_;
v___y_1054_ = v___y_1106_;
v___y_1055_ = v___x_1130_;
v___y_1056_ = v___x_1129_;
v___y_1057_ = v___y_1103_;
v___y_1058_ = v___y_1104_;
v___y_1059_ = v___x_1124_;
v___y_1060_ = v_quotContext_x3f_1114_;
v_a_1061_ = v_val_1133_;
goto v___jp_1050_;
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_a_1126_);
lean_dec_ref(v___x_1124_);
lean_dec(v_quotContext_x3f_1114_);
lean_dec(v___y_1106_);
lean_dec(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec(v_stx_616_);
v_a_1134_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1127_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1127_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v___x_1124_);
lean_dec(v_quotContext_x3f_1114_);
lean_dec(v___y_1106_);
lean_dec(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec(v_stx_616_);
v_a_1142_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1125_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1125_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec(v_kw_1099_);
lean_dec(v_stx_616_);
v_a_1153_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1107_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1107_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
v___jp_1161_:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_Syntax_getOptional_x3f(v___x_693_);
lean_dec(v___x_693_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_box(0);
v___y_1101_ = v___y_1166_;
v___y_1102_ = v___y_1162_;
v___y_1103_ = v___y_1163_;
v___y_1104_ = v___y_1164_;
v___y_1105_ = v___y_1165_;
v___y_1106_ = v___x_1168_;
goto v___jp_1100_;
}
else
{
lean_object* v_val_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
v_val_1169_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1167_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_val_1169_);
lean_dec(v___x_1167_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_val_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
v___y_1101_ = v___y_1166_;
v___y_1102_ = v___y_1162_;
v___y_1103_ = v___y_1163_;
v___y_1104_ = v___y_1164_;
v___y_1105_ = v___y_1165_;
v___y_1106_ = v___x_1174_;
goto v___jp_1100_;
}
}
}
}
v___jp_1177_:
{
lean_object* v___x_1181_; lean_object* v_cfg_1182_; lean_object* v___x_1183_; 
v___x_1181_ = lean_unsigned_to_nat(4u);
v_cfg_1182_ = l_Lean_Syntax_getArg(v_stx_616_, v___x_1181_);
v___x_1183_ = l_Lean_Syntax_getOptional_x3f(v___x_695_);
lean_dec(v___x_695_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_box(0);
v___y_1162_ = v_nameStx_x3f_1178_;
v___y_1163_ = v_cfg_1182_;
v___y_1164_ = v___y_1180_;
v___y_1165_ = v___y_1179_;
v___y_1166_ = v___x_1184_;
goto v___jp_1161_;
}
else
{
lean_object* v_val_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
v_val_1185_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1183_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_val_1185_);
lean_dec(v___x_1183_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_val_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
v___y_1162_ = v_nameStx_x3f_1178_;
v___y_1163_ = v_cfg_1182_;
v___y_1164_ = v___y_1180_;
v___y_1165_ = v___y_1179_;
v___y_1166_ = v___x_1190_;
goto v___jp_1161_;
}
}
}
}
}
v___jp_620_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_inc(v___y_643_);
lean_inc(v___y_639_);
v___x_645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_645_, 0, v___y_639_);
lean_ctor_set(v___x_645_, 1, v___y_643_);
lean_ctor_set(v___x_645_, 2, v___y_636_);
lean_inc(v___y_639_);
v___x_646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_646_, 0, v___y_639_);
lean_ctor_set(v___x_646_, 1, v___y_644_);
lean_inc_ref(v___x_645_);
lean_inc(v___y_639_);
v___x_647_ = l_Lean_Syntax_node1(v___y_639_, v___y_637_, v___x_645_);
v___x_648_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0));
v___x_649_ = l_Lean_Name_mkStr2(v___y_633_, v___x_648_);
lean_inc(v___y_639_);
v___x_650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_650_, 0, v___y_639_);
lean_ctor_set(v___x_650_, 1, v___x_648_);
v___x_651_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2));
v___x_652_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3));
lean_inc(v___y_639_);
v___x_653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_653_, 0, v___y_639_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
lean_inc(v___y_639_);
v___x_654_ = l_Lean_Syntax_node1(v___y_639_, v___x_651_, v___x_653_);
lean_inc(v___y_643_);
lean_inc(v___y_639_);
v___x_655_ = l_Lean_Syntax_node1(v___y_639_, v___y_643_, v___x_654_);
v___x_656_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4));
lean_inc(v___y_639_);
v___x_657_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_657_, 0, v___y_639_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5));
lean_inc(v___y_639_);
v___x_659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_659_, 0, v___y_639_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
lean_inc(v___y_639_);
v___x_660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_660_, 0, v___y_639_);
lean_ctor_set(v___x_660_, 1, v___y_630_);
v___x_661_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6));
lean_inc(v___y_639_);
v___x_662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_662_, 0, v___y_639_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
lean_inc(v___y_639_);
v___x_663_ = l_Lean_Syntax_node1(v___y_639_, v___x_651_, v___x_662_);
v___x_664_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7));
lean_inc(v___y_639_);
v___x_665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_665_, 0, v___y_639_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
lean_inc_ref(v___x_660_);
lean_inc(v___y_643_);
lean_inc(v___y_639_);
v___x_666_ = l_Lean_Syntax_node5(v___y_639_, v___y_643_, v___x_657_, v___x_659_, v___x_660_, v___x_663_, v___x_665_);
lean_inc_ref(v___x_645_);
lean_inc(v___y_639_);
v___x_667_ = l_Lean_Syntax_node4(v___y_639_, v___x_649_, v___x_650_, v___x_645_, v___x_655_, v___x_666_);
lean_inc(v___y_639_);
v___x_668_ = l_Lean_Syntax_node2(v___y_639_, v___y_635_, v___x_647_, v___x_667_);
lean_inc(v___y_643_);
lean_inc(v___y_639_);
v___x_669_ = l_Lean_Syntax_node1(v___y_639_, v___y_643_, v___x_668_);
lean_inc(v___y_639_);
v___x_670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_670_, 0, v___y_639_);
lean_ctor_set(v___x_670_, 1, v___y_625_);
lean_inc(v___y_639_);
v___x_671_ = l_Lean_Syntax_node3(v___y_639_, v___y_634_, v___x_646_, v___x_669_, v___x_670_);
lean_inc(v___y_639_);
v___x_672_ = l_Lean_Syntax_node1(v___y_639_, v___y_643_, v___x_671_);
lean_inc_ref_n(v___x_645_, 6);
lean_inc(v___y_639_);
v___x_673_ = l_Lean_Syntax_node7(v___y_639_, v___y_622_, v___x_645_, v___x_672_, v___x_645_, v___x_645_, v___x_645_, v___x_645_, v___x_645_);
lean_inc(v___y_639_);
v___x_674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_674_, 0, v___y_639_);
lean_ctor_set(v___x_674_, 1, v___y_623_);
v___x_675_ = lean_array_push(v___y_640_, v___y_638_);
v___x_676_ = lean_array_push(v___x_675_, v___y_621_);
v___x_677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_677_, 0, v___y_642_);
lean_ctor_set(v___x_677_, 1, v___y_641_);
lean_ctor_set(v___x_677_, 2, v___x_676_);
lean_inc_ref_n(v___x_645_, 2);
lean_inc(v___y_639_);
v___x_678_ = l_Lean_Syntax_node2(v___y_639_, v___y_632_, v___x_645_, v___x_645_);
v___x_679_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9));
v___x_680_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10));
lean_inc(v___y_639_);
v___x_681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_681_, 0, v___y_639_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
lean_inc(v___y_639_);
v___x_682_ = l_Lean_Syntax_node1(v___y_639_, v___x_679_, v___x_681_);
lean_inc_ref_n(v___x_645_, 2);
lean_inc(v___y_639_);
v___x_683_ = l_Lean_Syntax_node2(v___y_639_, v___y_628_, v___x_645_, v___x_645_);
lean_inc(v___y_639_);
v___x_684_ = l_Lean_Syntax_node4(v___y_639_, v___y_626_, v___x_660_, v___x_682_, v___x_683_, v___x_645_);
lean_inc(v___y_639_);
v___x_685_ = l_Lean_Syntax_node4(v___y_639_, v___y_627_, v___x_674_, v___x_677_, v___x_678_, v___x_684_);
v___x_686_ = l_Lean_Syntax_node2(v___y_639_, v___y_624_, v___x_673_, v___x_685_);
v___x_687_ = l_Lean_Elab_Command_elabCommand(v___x_686_, v___y_631_, v___y_629_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed(lean_object* v_stx_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(v_stx_1202_, v_a_1203_, v_a_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(lean_object* v_00_u03b1_1207_, lean_object* v_ref_1208_, lean_object* v_msg_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_1208_, v_msg_1209_, v___y_1210_, v___y_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___boxed(lean_object* v_00_u03b1_1214_, lean_object* v_ref_1215_, lean_object* v_msg_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(v_00_u03b1_1214_, v_ref_1215_, v_msg_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec(v_ref_1215_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(lean_object* v_msgData_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msgData_1221_, v___y_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(v_msgData_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(lean_object* v_00_u03b1_1231_, lean_object* v_msg_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_1232_, v___y_1233_, v___y_1234_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1237_, lean_object* v_msg_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(v_00_u03b1_1237_, v_msg_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(lean_object* v_msgData_1243_, lean_object* v_macroStack_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_1243_, v_macroStack_1244_, v___y_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1249_, lean_object* v_macroStack_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(v_msgData_1249_, v_macroStack_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1(){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1283_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1284_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12));
v___x_1285_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10));
v___x_1286_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed), 4, 0);
v___x_1287_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1283_, v___x_1284_, v___x_1285_, v___x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___boxed(lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
return v_res_1289_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3));
v___x_1298_ = l_String_toRawSubstring_x27(v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6));
v___x_1303_ = l_String_toRawSubstring_x27(v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12));
v___x_1316_ = l_String_toRawSubstring_x27(v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15));
v___x_1321_ = l_String_toRawSubstring_x27(v___x_1320_);
return v___x_1321_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21));
v___x_1329_ = l_String_toRawSubstring_x27(v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(lean_object* v_stx_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___x_1380_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; uint8_t v___x_1400_; 
v___x_1380_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1));
lean_inc(v_stx_1354_);
v___x_1400_ = l_Lean_Syntax_isOfKind(v_stx_1354_, v___x_1380_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1402_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1354_, v___x_1401_, v_a_1355_, v_a_1356_);
lean_dec(v_stx_1354_);
return v___x_1402_;
}
else
{
lean_object* v___x_1403_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; uint8_t v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v_wds_x3f_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v_wds_x3f_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v_pkg_x3f_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v_attrs_x3f_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v_doc_x3f_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1793_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1403_);
v___x_1794_ = l_Lean_Syntax_isNone(v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1793_);
v___x_1796_ = l_Lean_Syntax_matchesNull(v___x_1793_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_dec(v___x_1793_);
v___x_1797_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1798_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1354_, v___x_1797_, v_a_1355_, v_a_1356_);
lean_dec(v_stx_1354_);
return v___x_1798_;
}
else
{
lean_object* v_doc_x3f_1799_; lean_object* v___x_1800_; 
v_doc_x3f_1799_ = l_Lean_Syntax_getArg(v___x_1793_, v___x_1403_);
lean_dec(v___x_1793_);
v___x_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1800_, 0, v_doc_x3f_1799_);
v_doc_x3f_1781_ = v___x_1800_;
v___y_1782_ = v_a_1355_;
v___y_1783_ = v_a_1356_;
goto v___jp_1780_;
}
}
else
{
lean_object* v___x_1801_; 
lean_dec(v___x_1793_);
v___x_1801_ = lean_box(0);
v_doc_x3f_1781_ = v___x_1801_;
v___y_1782_ = v_a_1355_;
v___y_1783_ = v_a_1356_;
goto v___jp_1780_;
}
v___jp_1404_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_inc_ref(v___y_1405_);
v___x_1426_ = l_Array_append___redArg(v___y_1405_, v___y_1425_);
lean_dec_ref(v___y_1425_);
lean_inc(v___y_1422_);
lean_inc(v___y_1408_);
v___x_1427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1408_);
lean_ctor_set(v___x_1427_, 1, v___y_1422_);
lean_ctor_set(v___x_1427_, 2, v___x_1426_);
v___x_1428_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15));
lean_inc_ref(v___y_1411_);
lean_inc_ref(v___y_1407_);
lean_inc_ref(v___y_1420_);
v___x_1429_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1407_, v___y_1411_, v___x_1428_);
v___x_1430_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16));
lean_inc(v___y_1408_);
v___x_1431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___y_1408_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38));
v___x_1433_ = l_Lean_Syntax_SepArray_ofElems(v___x_1432_, v___y_1421_);
lean_dec_ref(v___y_1421_);
lean_inc_ref(v___y_1405_);
v___x_1434_ = l_Array_append___redArg(v___y_1405_, v___x_1433_);
lean_dec_ref(v___x_1433_);
lean_inc(v___y_1422_);
lean_inc(v___y_1408_);
v___x_1435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1435_, 0, v___y_1408_);
lean_ctor_set(v___x_1435_, 1, v___y_1422_);
lean_ctor_set(v___x_1435_, 2, v___x_1434_);
v___x_1436_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17));
lean_inc(v___y_1408_);
v___x_1437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___y_1408_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
lean_inc(v___y_1408_);
v___x_1438_ = l_Lean_Syntax_node3(v___y_1408_, v___x_1429_, v___x_1431_, v___x_1435_, v___x_1437_);
lean_inc(v___y_1422_);
lean_inc(v___y_1408_);
v___x_1439_ = l_Lean_Syntax_node1(v___y_1408_, v___y_1422_, v___x_1438_);
lean_inc_n(v___y_1415_, 5);
lean_inc(v___y_1408_);
v___x_1440_ = l_Lean_Syntax_node7(v___y_1408_, v___y_1419_, v___x_1427_, v___x_1439_, v___y_1415_, v___y_1415_, v___y_1415_, v___y_1415_, v___y_1415_);
v___x_1441_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5));
lean_inc_ref(v___y_1409_);
lean_inc_ref(v___y_1407_);
lean_inc_ref(v___y_1420_);
v___x_1442_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1407_, v___y_1409_, v___x_1441_);
v___x_1443_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6));
lean_inc(v___y_1408_);
v___x_1444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___y_1408_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
lean_inc_ref(v___y_1409_);
lean_inc_ref(v___y_1407_);
lean_inc_ref(v___y_1420_);
v___x_1446_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1407_, v___y_1409_, v___x_1445_);
v___x_1447_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4);
v___x_1448_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5));
lean_inc(v___y_1406_);
lean_inc(v___y_1423_);
v___x_1449_ = l_Lean_addMacroScope(v___y_1423_, v___x_1448_, v___y_1406_);
lean_inc(v___y_1416_);
lean_inc(v___y_1408_);
v___x_1450_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1450_, 0, v___y_1408_);
lean_ctor_set(v___x_1450_, 1, v___x_1447_);
lean_ctor_set(v___x_1450_, 2, v___x_1449_);
lean_ctor_set(v___x_1450_, 3, v___y_1416_);
lean_inc(v___y_1415_);
lean_inc(v___y_1408_);
v___x_1451_ = l_Lean_Syntax_node2(v___y_1408_, v___x_1446_, v___x_1450_, v___y_1415_);
v___x_1452_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
lean_inc_ref(v___y_1407_);
lean_inc_ref(v___y_1420_);
v___x_1453_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1407_, v___y_1409_, v___x_1452_);
v___x_1454_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
lean_inc_ref(v___y_1411_);
lean_inc_ref(v___y_1407_);
lean_inc_ref(v___y_1420_);
v___x_1455_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1407_, v___y_1411_, v___x_1454_);
v___x_1456_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
lean_inc(v___y_1408_);
v___x_1457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___y_1408_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7);
v___x_1459_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8));
lean_inc(v___y_1406_);
lean_inc(v___y_1423_);
v___x_1460_ = l_Lean_addMacroScope(v___y_1423_, v___x_1459_, v___y_1406_);
v___x_1461_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10));
v___x_1462_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11));
lean_inc(v___y_1416_);
v___x_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v___y_1416_);
v___x_1464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1461_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
lean_inc(v___y_1408_);
v___x_1465_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1465_, 0, v___y_1408_);
lean_ctor_set(v___x_1465_, 1, v___x_1458_);
lean_ctor_set(v___x_1465_, 2, v___x_1460_);
lean_ctor_set(v___x_1465_, 3, v___x_1464_);
lean_inc(v___y_1408_);
v___x_1466_ = l_Lean_Syntax_node2(v___y_1408_, v___x_1455_, v___x_1457_, v___x_1465_);
lean_inc(v___y_1422_);
lean_inc(v___y_1408_);
v___x_1467_ = l_Lean_Syntax_node1(v___y_1408_, v___y_1422_, v___x_1466_);
lean_inc(v___y_1415_);
lean_inc(v___y_1408_);
v___x_1468_ = l_Lean_Syntax_node2(v___y_1408_, v___x_1453_, v___y_1415_, v___x_1467_);
v___x_1469_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37));
lean_inc(v___y_1408_);
v___x_1470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___y_1408_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
lean_inc_ref(v___y_1411_);
lean_inc_ref(v___y_1407_);
lean_inc_ref(v___y_1420_);
v___x_1472_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1407_, v___y_1411_, v___x_1471_);
v___x_1473_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
lean_inc(v___y_1408_);
v___x_1474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___y_1408_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31));
lean_inc_ref(v___y_1411_);
lean_inc_ref(v___y_1407_);
lean_inc_ref(v___y_1420_);
v___x_1476_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1407_, v___y_1411_, v___x_1475_);
v___x_1477_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31));
lean_inc_ref(v___y_1411_);
lean_inc_ref(v___y_1407_);
lean_inc_ref(v___y_1420_);
v___x_1478_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1407_, v___y_1411_, v___x_1477_);
v___x_1479_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32));
lean_inc_ref(v___y_1411_);
lean_inc_ref(v___y_1407_);
lean_inc_ref(v___y_1420_);
v___x_1480_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1407_, v___y_1411_, v___x_1479_);
v___x_1481_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13);
v___x_1482_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14));
lean_inc(v___y_1406_);
lean_inc(v___y_1423_);
v___x_1483_ = l_Lean_addMacroScope(v___y_1423_, v___x_1482_, v___y_1406_);
lean_inc(v___y_1416_);
lean_inc(v___y_1408_);
v___x_1484_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1484_, 0, v___y_1408_);
lean_ctor_set(v___x_1484_, 1, v___x_1481_);
lean_ctor_set(v___x_1484_, 2, v___x_1483_);
lean_ctor_set(v___x_1484_, 3, v___y_1416_);
lean_inc(v___y_1415_);
lean_inc(v___x_1480_);
lean_inc(v___y_1408_);
v___x_1485_ = l_Lean_Syntax_node2(v___y_1408_, v___x_1480_, v___x_1484_, v___y_1415_);
v___x_1486_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36));
lean_inc_ref(v___y_1411_);
lean_inc_ref(v___y_1407_);
lean_inc_ref(v___y_1420_);
v___x_1487_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1407_, v___y_1411_, v___x_1486_);
v___x_1488_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9));
v___x_1489_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10));
lean_inc(v___y_1408_);
v___x_1490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___y_1408_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
lean_inc(v___y_1408_);
v___x_1491_ = l_Lean_Syntax_node1(v___y_1408_, v___x_1488_, v___x_1490_);
lean_inc(v___y_1415_);
lean_inc_ref(v___x_1470_);
lean_inc(v___x_1487_);
lean_inc(v___y_1408_);
v___x_1492_ = l_Lean_Syntax_node3(v___y_1408_, v___x_1487_, v___x_1470_, v___y_1415_, v___x_1491_);
lean_inc_n(v___y_1415_, 2);
lean_inc(v___y_1422_);
lean_inc(v___y_1408_);
v___x_1493_ = l_Lean_Syntax_node3(v___y_1408_, v___y_1422_, v___y_1415_, v___y_1415_, v___x_1492_);
lean_inc(v___x_1478_);
lean_inc(v___y_1408_);
v___x_1494_ = l_Lean_Syntax_node2(v___y_1408_, v___x_1478_, v___x_1485_, v___x_1493_);
lean_inc(v___y_1408_);
v___x_1495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___y_1408_);
lean_ctor_set(v___x_1495_, 1, v___x_1432_);
v___x_1496_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16);
v___x_1497_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17));
v___x_1498_ = l_Lean_addMacroScope(v___y_1423_, v___x_1497_, v___y_1406_);
lean_inc(v___y_1408_);
v___x_1499_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1499_, 0, v___y_1408_);
lean_ctor_set(v___x_1499_, 1, v___x_1496_);
lean_ctor_set(v___x_1499_, 2, v___x_1498_);
lean_ctor_set(v___x_1499_, 3, v___y_1416_);
lean_inc(v___y_1415_);
lean_inc(v___y_1408_);
v___x_1500_ = l_Lean_Syntax_node2(v___y_1408_, v___x_1480_, v___x_1499_, v___y_1415_);
v___x_1501_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18));
lean_inc_ref(v___y_1411_);
lean_inc_ref(v___y_1407_);
lean_inc_ref(v___y_1420_);
v___x_1502_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1407_, v___y_1411_, v___x_1501_);
lean_inc(v___y_1408_);
v___x_1503_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___y_1408_);
lean_ctor_set(v___x_1503_, 1, v___x_1501_);
v___x_1504_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19));
lean_inc_ref(v___y_1411_);
lean_inc_ref(v___y_1407_);
lean_inc_ref(v___y_1420_);
v___x_1505_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1407_, v___y_1411_, v___x_1504_);
lean_inc(v___y_1422_);
lean_inc(v___y_1408_);
v___x_1506_ = l_Lean_Syntax_node1(v___y_1408_, v___y_1422_, v___y_1410_);
v___x_1507_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20));
lean_inc(v___y_1408_);
v___x_1508_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___y_1408_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
lean_inc(v___y_1415_);
lean_inc(v___y_1408_);
v___x_1509_ = l_Lean_Syntax_node4(v___y_1408_, v___x_1505_, v___x_1506_, v___y_1415_, v___x_1508_, v___y_1417_);
lean_inc(v___y_1408_);
v___x_1510_ = l_Lean_Syntax_node2(v___y_1408_, v___x_1502_, v___x_1503_, v___x_1509_);
lean_inc(v___y_1415_);
lean_inc_ref(v___x_1470_);
lean_inc(v___y_1408_);
v___x_1511_ = l_Lean_Syntax_node3(v___y_1408_, v___x_1487_, v___x_1470_, v___y_1415_, v___x_1510_);
lean_inc_n(v___y_1415_, 2);
lean_inc(v___y_1422_);
lean_inc(v___y_1408_);
v___x_1512_ = l_Lean_Syntax_node3(v___y_1408_, v___y_1422_, v___y_1415_, v___y_1415_, v___x_1511_);
lean_inc(v___y_1408_);
v___x_1513_ = l_Lean_Syntax_node2(v___y_1408_, v___x_1478_, v___x_1500_, v___x_1512_);
lean_inc(v___y_1422_);
lean_inc(v___y_1408_);
v___x_1514_ = l_Lean_Syntax_node3(v___y_1408_, v___y_1422_, v___x_1494_, v___x_1495_, v___x_1513_);
lean_inc(v___y_1408_);
v___x_1515_ = l_Lean_Syntax_node1(v___y_1408_, v___x_1476_, v___x_1514_);
v___x_1516_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45));
v___x_1517_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1407_, v___y_1411_, v___x_1516_);
lean_inc(v___y_1415_);
lean_inc(v___y_1408_);
v___x_1518_ = l_Lean_Syntax_node1(v___y_1408_, v___x_1517_, v___y_1415_);
v___x_1519_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46));
lean_inc(v___y_1408_);
v___x_1520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___y_1408_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
lean_inc_n(v___y_1415_, 2);
lean_inc(v___y_1408_);
v___x_1521_ = l_Lean_Syntax_node6(v___y_1408_, v___x_1472_, v___x_1474_, v___y_1415_, v___x_1515_, v___x_1518_, v___y_1415_, v___x_1520_);
lean_inc_n(v___y_1415_, 2);
lean_inc(v___y_1408_);
v___x_1522_ = l_Lean_Syntax_node2(v___y_1408_, v___y_1412_, v___y_1415_, v___y_1415_);
if (lean_obj_tag(v___y_1424_) == 1)
{
lean_object* v_val_1523_; lean_object* v___x_1524_; 
v_val_1523_ = lean_ctor_get(v___y_1424_, 0);
lean_inc(v_val_1523_);
lean_dec_ref(v___y_1424_);
v___x_1524_ = l_Array_mkArray1___redArg(v_val_1523_);
v___y_1358_ = v___x_1444_;
v___y_1359_ = v___x_1440_;
v___y_1360_ = v___y_1405_;
v___y_1361_ = v___x_1522_;
v___y_1362_ = v___y_1408_;
v___y_1363_ = v___x_1521_;
v___y_1364_ = v___y_1414_;
v___y_1365_ = v___y_1413_;
v___y_1366_ = v___y_1415_;
v___y_1367_ = v___y_1418_;
v___y_1368_ = v___x_1470_;
v___y_1369_ = v___x_1442_;
v___y_1370_ = v___y_1422_;
v___y_1371_ = v___x_1451_;
v___y_1372_ = v___x_1468_;
v___y_1373_ = v___x_1524_;
goto v___jp_1357_;
}
else
{
lean_object* v___x_1525_; 
lean_dec(v___y_1424_);
v___x_1525_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___y_1358_ = v___x_1444_;
v___y_1359_ = v___x_1440_;
v___y_1360_ = v___y_1405_;
v___y_1361_ = v___x_1522_;
v___y_1362_ = v___y_1408_;
v___y_1363_ = v___x_1521_;
v___y_1364_ = v___y_1414_;
v___y_1365_ = v___y_1413_;
v___y_1366_ = v___y_1415_;
v___y_1367_ = v___y_1418_;
v___y_1368_ = v___x_1470_;
v___y_1369_ = v___x_1442_;
v___y_1370_ = v___y_1422_;
v___y_1371_ = v___x_1451_;
v___y_1372_ = v___x_1468_;
v___y_1373_ = v___x_1525_;
goto v___jp_1357_;
}
}
v___jp_1526_:
{
lean_object* v_methods_1542_; lean_object* v_quotContext_1543_; lean_object* v_currMacroScope_1544_; lean_object* v_currRecDepth_1545_; lean_object* v_maxRecDepth_1546_; lean_object* v_ref_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1598_; 
v_methods_1542_ = lean_ctor_get(v___y_1540_, 0);
v_quotContext_1543_ = lean_ctor_get(v___y_1540_, 1);
v_currMacroScope_1544_ = lean_ctor_get(v___y_1540_, 2);
v_currRecDepth_1545_ = lean_ctor_get(v___y_1540_, 3);
v_maxRecDepth_1546_ = lean_ctor_get(v___y_1540_, 4);
v_ref_1547_ = lean_ctor_get(v___y_1540_, 5);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___y_1540_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1549_ = v___y_1540_;
v_isShared_1550_ = v_isSharedCheck_1598_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_ref_1547_);
lean_inc(v_maxRecDepth_1546_);
lean_inc(v_currRecDepth_1545_);
lean_inc(v_currMacroScope_1544_);
lean_inc(v_quotContext_1543_);
lean_inc(v_methods_1542_);
lean_dec(v___y_1540_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1598_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_ref_1551_; lean_object* v___x_1553_; 
v_ref_1551_ = l_Lean_replaceRef(v___y_1538_, v_ref_1547_);
lean_dec(v_ref_1547_);
lean_dec(v___y_1538_);
lean_inc(v_ref_1551_);
lean_inc(v_currMacroScope_1544_);
lean_inc(v_quotContext_1543_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 5, v_ref_1551_);
v___x_1553_ = v___x_1549_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_methods_1542_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_quotContext_1543_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_currMacroScope_1544_);
lean_ctor_set(v_reuseFailAlloc_1597_, 3, v_currRecDepth_1545_);
lean_ctor_set(v_reuseFailAlloc_1597_, 4, v_maxRecDepth_1546_);
lean_ctor_set(v_reuseFailAlloc_1597_, 5, v_ref_1551_);
v___x_1553_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lake_DSL_expandOptSimpleBinder(v___y_1531_, v___x_1553_, v___y_1541_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v_a_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
v_a_1556_ = lean_ctor_get(v___x_1554_, 1);
lean_inc(v_a_1556_);
lean_dec_ref(v___x_1554_);
v___x_1557_ = l_Lean_SourceInfo_fromRef(v_ref_1551_, v___y_1533_);
lean_dec(v_ref_1551_);
v___x_1558_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_1559_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47));
lean_inc_ref(v___y_1529_);
lean_inc_ref(v___y_1532_);
v___x_1560_ = l_Lean_Name_mkStr4(v___y_1532_, v___y_1529_, v___x_1558_, v___x_1559_);
v___x_1561_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48));
lean_inc_ref(v___y_1529_);
lean_inc_ref(v___y_1532_);
v___x_1562_ = l_Lean_Name_mkStr4(v___y_1532_, v___y_1529_, v___x_1558_, v___x_1561_);
v___x_1563_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_1564_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc(v___x_1557_);
v___x_1565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1557_);
lean_ctor_set(v___x_1565_, 1, v___x_1563_);
lean_ctor_set(v___x_1565_, 2, v___x_1564_);
lean_inc_ref(v___x_1565_);
lean_inc(v___x_1557_);
v___x_1566_ = l_Lean_Syntax_node1(v___x_1557_, v___x_1562_, v___x_1565_);
v___x_1567_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53));
v___x_1568_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54));
lean_inc_ref(v___y_1529_);
lean_inc_ref(v___y_1532_);
v___x_1569_ = l_Lean_Name_mkStr4(v___y_1532_, v___y_1529_, v___x_1567_, v___x_1568_);
v___x_1570_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22);
v___x_1571_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24));
lean_inc(v_currMacroScope_1544_);
lean_inc(v_quotContext_1543_);
v___x_1572_ = l_Lean_addMacroScope(v_quotContext_1543_, v___x_1571_, v_currMacroScope_1544_);
v___x_1573_ = lean_box(0);
lean_inc(v___x_1557_);
v___x_1574_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1557_);
lean_ctor_set(v___x_1574_, 1, v___x_1570_);
lean_ctor_set(v___x_1574_, 2, v___x_1572_);
lean_ctor_set(v___x_1574_, 3, v___x_1573_);
lean_inc_ref(v___x_1565_);
lean_inc(v___x_1557_);
v___x_1575_ = l_Lean_Syntax_node2(v___x_1557_, v___x_1569_, v___x_1574_, v___x_1565_);
lean_inc(v___x_1557_);
v___x_1576_ = l_Lean_Syntax_node2(v___x_1557_, v___x_1560_, v___x_1566_, v___x_1575_);
v___x_1577_ = lean_mk_empty_array_with_capacity(v___y_1530_);
v___x_1578_ = lean_array_push(v___x_1577_, v___x_1576_);
v___x_1579_ = l_Lake_DSL_expandAttrs(v___y_1535_);
v___x_1580_ = l_Array_append___redArg(v___x_1578_, v___x_1579_);
lean_dec_ref(v___x_1579_);
v___x_1581_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref(v___y_1534_);
lean_inc_ref(v___y_1529_);
lean_inc_ref(v___y_1532_);
v___x_1582_ = l_Lean_Name_mkStr4(v___y_1532_, v___y_1529_, v___y_1534_, v___x_1581_);
v___x_1583_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
lean_inc_ref(v___y_1534_);
lean_inc_ref(v___y_1529_);
lean_inc_ref(v___y_1532_);
v___x_1584_ = l_Lean_Name_mkStr4(v___y_1532_, v___y_1529_, v___y_1534_, v___x_1583_);
if (lean_obj_tag(v___y_1527_) == 1)
{
lean_object* v_val_1585_; lean_object* v___x_1586_; 
v_val_1585_ = lean_ctor_get(v___y_1527_, 0);
lean_inc(v_val_1585_);
lean_dec_ref(v___y_1527_);
v___x_1586_ = l_Array_mkArray1___redArg(v_val_1585_);
v___y_1405_ = v___x_1564_;
v___y_1406_ = v_currMacroScope_1544_;
v___y_1407_ = v___y_1529_;
v___y_1408_ = v___x_1557_;
v___y_1409_ = v___y_1534_;
v___y_1410_ = v_a_1555_;
v___y_1411_ = v___x_1558_;
v___y_1412_ = v___y_1536_;
v___y_1413_ = v___x_1582_;
v___y_1414_ = v___y_1537_;
v___y_1415_ = v___x_1565_;
v___y_1416_ = v___x_1573_;
v___y_1417_ = v___y_1528_;
v___y_1418_ = v_a_1556_;
v___y_1419_ = v___x_1584_;
v___y_1420_ = v___y_1532_;
v___y_1421_ = v___x_1580_;
v___y_1422_ = v___x_1563_;
v___y_1423_ = v_quotContext_1543_;
v___y_1424_ = v_wds_x3f_1539_;
v___y_1425_ = v___x_1586_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1587_; 
lean_dec(v___y_1527_);
v___x_1587_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___y_1405_ = v___x_1564_;
v___y_1406_ = v_currMacroScope_1544_;
v___y_1407_ = v___y_1529_;
v___y_1408_ = v___x_1557_;
v___y_1409_ = v___y_1534_;
v___y_1410_ = v_a_1555_;
v___y_1411_ = v___x_1558_;
v___y_1412_ = v___y_1536_;
v___y_1413_ = v___x_1582_;
v___y_1414_ = v___y_1537_;
v___y_1415_ = v___x_1565_;
v___y_1416_ = v___x_1573_;
v___y_1417_ = v___y_1528_;
v___y_1418_ = v_a_1556_;
v___y_1419_ = v___x_1584_;
v___y_1420_ = v___y_1532_;
v___y_1421_ = v___x_1580_;
v___y_1422_ = v___x_1563_;
v___y_1423_ = v_quotContext_1543_;
v___y_1424_ = v_wds_x3f_1539_;
v___y_1425_ = v___x_1587_;
goto v___jp_1404_;
}
}
else
{
lean_object* v_a_1588_; lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v_ref_1551_);
lean_dec(v_currMacroScope_1544_);
lean_dec(v_quotContext_1543_);
lean_dec(v_wds_x3f_1539_);
lean_dec(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec_ref(v___y_1532_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec(v___y_1527_);
v_a_1588_ = lean_ctor_get(v___x_1554_, 0);
v_a_1589_ = lean_ctor_get(v___x_1554_, 1);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1554_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_inc(v_a_1588_);
lean_dec(v___x_1554_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1588_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
}
v___jp_1599_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_inc_ref(v___y_1611_);
v___x_1614_ = l_Array_append___redArg(v___y_1611_, v___y_1613_);
lean_dec_ref(v___y_1613_);
lean_inc(v___y_1603_);
lean_inc(v___y_1600_);
v___x_1615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1615_, 0, v___y_1600_);
lean_ctor_set(v___x_1615_, 1, v___y_1603_);
lean_ctor_set(v___x_1615_, 2, v___x_1614_);
v___x_1616_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_1617_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25));
lean_inc_ref(v___y_1601_);
lean_inc_ref(v___y_1610_);
v___x_1618_ = l_Lean_Name_mkStr4(v___y_1610_, v___y_1601_, v___x_1616_, v___x_1617_);
v___x_1619_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37));
lean_inc(v___y_1600_);
v___x_1620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___y_1600_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
lean_inc(v___y_1600_);
v___x_1621_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___y_1600_);
lean_ctor_set(v___x_1621_, 1, v___y_1604_);
lean_inc(v___y_1600_);
v___x_1622_ = l_Lean_Syntax_node2(v___y_1600_, v___y_1607_, v___x_1621_, v___y_1609_);
v___x_1623_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26));
v___x_1624_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27));
v___x_1625_ = l_Lean_Name_mkStr4(v___y_1610_, v___y_1601_, v___x_1623_, v___x_1624_);
lean_inc_ref(v___y_1611_);
lean_inc(v___y_1603_);
lean_inc(v___y_1600_);
v___x_1626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1626_, 0, v___y_1600_);
lean_ctor_set(v___x_1626_, 1, v___y_1603_);
lean_ctor_set(v___x_1626_, 2, v___y_1611_);
lean_inc_ref(v___x_1626_);
lean_inc(v___y_1600_);
v___x_1627_ = l_Lean_Syntax_node2(v___y_1600_, v___x_1625_, v___x_1626_, v___x_1626_);
if (lean_obj_tag(v___y_1606_) == 1)
{
lean_object* v_val_1628_; lean_object* v___x_1629_; 
v_val_1628_ = lean_ctor_get(v___y_1606_, 0);
lean_inc(v_val_1628_);
lean_dec_ref(v___y_1606_);
v___x_1629_ = l_Array_mkArray1___redArg(v_val_1628_);
v___y_1382_ = v___y_1600_;
v___y_1383_ = v___y_1608_;
v___y_1384_ = v___x_1620_;
v___y_1385_ = v___x_1627_;
v___y_1386_ = v___x_1615_;
v___y_1387_ = v___x_1622_;
v___y_1388_ = v___y_1611_;
v___y_1389_ = v___x_1618_;
v___y_1390_ = v___y_1602_;
v___y_1391_ = v___y_1605_;
v___y_1392_ = v___y_1612_;
v___y_1393_ = v___y_1603_;
v___y_1394_ = v___x_1629_;
goto v___jp_1381_;
}
else
{
lean_object* v___x_1630_; 
lean_dec(v___y_1606_);
v___x_1630_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___y_1382_ = v___y_1600_;
v___y_1383_ = v___y_1608_;
v___y_1384_ = v___x_1620_;
v___y_1385_ = v___x_1627_;
v___y_1386_ = v___x_1615_;
v___y_1387_ = v___x_1622_;
v___y_1388_ = v___y_1611_;
v___y_1389_ = v___x_1618_;
v___y_1390_ = v___y_1602_;
v___y_1391_ = v___y_1605_;
v___y_1392_ = v___y_1612_;
v___y_1393_ = v___y_1603_;
v___y_1394_ = v___x_1630_;
goto v___jp_1381_;
}
}
v___jp_1631_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_inc_ref(v___y_1643_);
v___x_1646_ = l_Array_append___redArg(v___y_1643_, v___y_1645_);
lean_dec_ref(v___y_1645_);
lean_inc(v___y_1635_);
lean_inc(v___y_1632_);
v___x_1647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1647_, 0, v___y_1632_);
lean_ctor_set(v___x_1647_, 1, v___y_1635_);
lean_ctor_set(v___x_1647_, 2, v___x_1646_);
v___x_1648_ = l_Lean_SourceInfo_fromRef(v___y_1644_, v___x_1400_);
lean_dec(v___y_1644_);
v___x_1649_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23));
v___x_1650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
if (lean_obj_tag(v___y_1641_) == 1)
{
lean_object* v_val_1651_; lean_object* v___x_1652_; 
v_val_1651_ = lean_ctor_get(v___y_1641_, 0);
lean_inc(v_val_1651_);
lean_dec_ref(v___y_1641_);
v___x_1652_ = l_Array_mkArray1___redArg(v_val_1651_);
v___y_1600_ = v___y_1632_;
v___y_1601_ = v___y_1633_;
v___y_1602_ = v___y_1634_;
v___y_1603_ = v___y_1635_;
v___y_1604_ = v___y_1636_;
v___y_1605_ = v___x_1650_;
v___y_1606_ = v___y_1637_;
v___y_1607_ = v___y_1638_;
v___y_1608_ = v___y_1639_;
v___y_1609_ = v___y_1640_;
v___y_1610_ = v___y_1642_;
v___y_1611_ = v___y_1643_;
v___y_1612_ = v___x_1647_;
v___y_1613_ = v___x_1652_;
goto v___jp_1599_;
}
else
{
lean_object* v___x_1653_; 
lean_dec(v___y_1641_);
v___x_1653_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___y_1600_ = v___y_1632_;
v___y_1601_ = v___y_1633_;
v___y_1602_ = v___y_1634_;
v___y_1603_ = v___y_1635_;
v___y_1604_ = v___y_1636_;
v___y_1605_ = v___x_1650_;
v___y_1606_ = v___y_1637_;
v___y_1607_ = v___y_1638_;
v___y_1608_ = v___y_1639_;
v___y_1609_ = v___y_1640_;
v___y_1610_ = v___y_1642_;
v___y_1611_ = v___y_1643_;
v___y_1612_ = v___x_1647_;
v___y_1613_ = v___x_1653_;
goto v___jp_1599_;
}
}
v___jp_1654_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_inc_ref(v___y_1665_);
v___x_1669_ = l_Array_append___redArg(v___y_1665_, v___y_1668_);
lean_dec_ref(v___y_1668_);
lean_inc(v___y_1658_);
lean_inc(v___y_1655_);
v___x_1670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1670_, 0, v___y_1655_);
lean_ctor_set(v___x_1670_, 1, v___y_1658_);
lean_ctor_set(v___x_1670_, 2, v___x_1669_);
if (lean_obj_tag(v___y_1666_) == 1)
{
lean_object* v_val_1671_; lean_object* v___x_1672_; 
v_val_1671_ = lean_ctor_get(v___y_1666_, 0);
lean_inc(v_val_1671_);
lean_dec_ref(v___y_1666_);
v___x_1672_ = l_Array_mkArray1___redArg(v_val_1671_);
v___y_1632_ = v___y_1655_;
v___y_1633_ = v___y_1656_;
v___y_1634_ = v___y_1657_;
v___y_1635_ = v___y_1658_;
v___y_1636_ = v___y_1659_;
v___y_1637_ = v___y_1660_;
v___y_1638_ = v___y_1661_;
v___y_1639_ = v___x_1670_;
v___y_1640_ = v___y_1662_;
v___y_1641_ = v___y_1663_;
v___y_1642_ = v___y_1664_;
v___y_1643_ = v___y_1665_;
v___y_1644_ = v___y_1667_;
v___y_1645_ = v___x_1672_;
goto v___jp_1631_;
}
else
{
lean_object* v___x_1673_; 
lean_dec(v___y_1666_);
v___x_1673_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___y_1632_ = v___y_1655_;
v___y_1633_ = v___y_1656_;
v___y_1634_ = v___y_1657_;
v___y_1635_ = v___y_1658_;
v___y_1636_ = v___y_1659_;
v___y_1637_ = v___y_1660_;
v___y_1638_ = v___y_1661_;
v___y_1639_ = v___x_1670_;
v___y_1640_ = v___y_1662_;
v___y_1641_ = v___y_1663_;
v___y_1642_ = v___y_1664_;
v___y_1643_ = v___y_1665_;
v___y_1644_ = v___y_1667_;
v___y_1645_ = v___x_1673_;
goto v___jp_1631_;
}
}
v___jp_1674_:
{
lean_object* v_ref_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_ref_1687_ = lean_ctor_get(v___y_1685_, 5);
lean_inc(v_ref_1687_);
lean_dec_ref(v___y_1685_);
v___x_1688_ = 0;
v___x_1689_ = l_Lean_SourceInfo_fromRef(v_ref_1687_, v___x_1688_);
lean_dec(v_ref_1687_);
v___x_1690_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_1691_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
if (lean_obj_tag(v___y_1676_) == 1)
{
lean_object* v_val_1692_; lean_object* v___x_1693_; 
v_val_1692_ = lean_ctor_get(v___y_1676_, 0);
lean_inc(v_val_1692_);
lean_dec_ref(v___y_1676_);
v___x_1693_ = l_Array_mkArray1___redArg(v_val_1692_);
v___y_1655_ = v___x_1689_;
v___y_1656_ = v___y_1678_;
v___y_1657_ = v___y_1686_;
v___y_1658_ = v___x_1690_;
v___y_1659_ = v___y_1683_;
v___y_1660_ = v_wds_x3f_1684_;
v___y_1661_ = v___y_1675_;
v___y_1662_ = v___y_1677_;
v___y_1663_ = v___y_1679_;
v___y_1664_ = v___y_1680_;
v___y_1665_ = v___x_1691_;
v___y_1666_ = v___y_1681_;
v___y_1667_ = v___y_1682_;
v___y_1668_ = v___x_1693_;
goto v___jp_1654_;
}
else
{
lean_object* v___x_1694_; 
lean_dec(v___y_1676_);
v___x_1694_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___y_1655_ = v___x_1689_;
v___y_1656_ = v___y_1678_;
v___y_1657_ = v___y_1686_;
v___y_1658_ = v___x_1690_;
v___y_1659_ = v___y_1683_;
v___y_1660_ = v_wds_x3f_1684_;
v___y_1661_ = v___y_1675_;
v___y_1662_ = v___y_1677_;
v___y_1663_ = v___y_1679_;
v___y_1664_ = v___y_1680_;
v___y_1665_ = v___x_1691_;
v___y_1666_ = v___y_1681_;
v___y_1667_ = v___y_1682_;
v___y_1668_ = v___x_1694_;
goto v___jp_1654_;
}
}
v___jp_1695_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1705_ = lean_unsigned_to_nat(4u);
v___x_1706_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1705_);
v___x_1707_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26));
lean_inc(v___x_1706_);
v___x_1708_ = l_Lean_Syntax_isOfKind(v___x_1706_, v___x_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1709_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1710_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_1711_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_1712_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27));
lean_inc(v___x_1706_);
v___x_1713_ = l_Lean_Syntax_isOfKind(v___x_1706_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec(v___x_1706_);
lean_dec(v_pkg_x3f_1702_);
lean_dec(v___y_1701_);
lean_dec(v___y_1699_);
lean_dec(v___y_1696_);
v___x_1714_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1715_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1354_, v___x_1714_, v___y_1703_, v___y_1704_);
lean_dec(v_stx_1354_);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1716_ = l_Lean_Syntax_getArg(v___x_1706_, v___y_1700_);
v___x_1717_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28));
lean_inc(v___x_1716_);
v___x_1718_ = l_Lean_Syntax_isOfKind(v___x_1716_, v___x_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_dec(v___x_1716_);
lean_dec(v___x_1706_);
lean_dec(v_pkg_x3f_1702_);
lean_dec(v___y_1701_);
lean_dec(v___y_1699_);
lean_dec(v___y_1696_);
v___x_1719_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1720_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1354_, v___x_1719_, v___y_1703_, v___y_1704_);
lean_dec(v_stx_1354_);
return v___x_1720_;
}
else
{
lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1721_ = l_Lean_Syntax_getArg(v___x_1716_, v___x_1403_);
v___x_1722_ = l_Lean_Syntax_matchesNull(v___x_1721_, v___x_1403_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec(v___x_1716_);
lean_dec(v___x_1706_);
lean_dec(v_pkg_x3f_1702_);
lean_dec(v___y_1701_);
lean_dec(v___y_1699_);
lean_dec(v___y_1696_);
v___x_1723_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1724_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1354_, v___x_1723_, v___y_1703_, v___y_1704_);
lean_dec(v_stx_1354_);
return v___x_1724_;
}
else
{
lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1725_ = l_Lean_Syntax_getArg(v___x_1716_, v___y_1698_);
lean_dec(v___x_1716_);
v___x_1726_ = l_Lean_Syntax_matchesNull(v___x_1725_, v___x_1403_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
lean_dec(v___x_1706_);
lean_dec(v_pkg_x3f_1702_);
lean_dec(v___y_1701_);
lean_dec(v___y_1699_);
lean_dec(v___y_1696_);
v___x_1727_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1728_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1354_, v___x_1727_, v___y_1703_, v___y_1704_);
lean_dec(v_stx_1354_);
return v___x_1728_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1729_ = l_Lean_Syntax_getArg(v___x_1706_, v___y_1698_);
v___x_1730_ = l_Lean_Syntax_getArg(v___x_1706_, v___y_1697_);
lean_dec(v___x_1706_);
v___x_1731_ = l_Lean_Syntax_isNone(v___x_1730_);
if (v___x_1731_ == 0)
{
uint8_t v___x_1732_; 
lean_inc(v___x_1730_);
v___x_1732_ = l_Lean_Syntax_matchesNull(v___x_1730_, v___y_1698_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_dec(v___x_1730_);
lean_dec(v___x_1729_);
lean_dec(v_pkg_x3f_1702_);
lean_dec(v___y_1701_);
lean_dec(v___y_1699_);
lean_dec(v___y_1696_);
v___x_1733_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1734_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1354_, v___x_1733_, v___y_1703_, v___y_1704_);
lean_dec(v_stx_1354_);
return v___x_1734_;
}
else
{
lean_object* v_wds_x3f_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v_wds_x3f_1735_ = l_Lean_Syntax_getArg(v___x_1730_, v___x_1403_);
lean_dec(v___x_1730_);
v___x_1736_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_1735_);
v___x_1737_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v_wds_x3f_1735_);
lean_dec(v___x_1729_);
lean_dec(v_pkg_x3f_1702_);
lean_dec(v___y_1701_);
lean_dec(v___y_1699_);
lean_dec(v___y_1696_);
v___x_1738_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1739_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1354_, v___x_1738_, v___y_1703_, v___y_1704_);
lean_dec(v_stx_1354_);
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; 
lean_dec(v_stx_1354_);
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v_wds_x3f_1735_);
v___y_1527_ = v___y_1696_;
v___y_1528_ = v___x_1729_;
v___y_1529_ = v___x_1710_;
v___y_1530_ = v___y_1698_;
v___y_1531_ = v_pkg_x3f_1702_;
v___y_1532_ = v___x_1709_;
v___y_1533_ = v___x_1708_;
v___y_1534_ = v___x_1711_;
v___y_1535_ = v___y_1699_;
v___y_1536_ = v___x_1717_;
v___y_1537_ = v___x_1712_;
v___y_1538_ = v___y_1701_;
v_wds_x3f_1539_ = v___x_1740_;
v___y_1540_ = v___y_1703_;
v___y_1541_ = v___y_1704_;
goto v___jp_1526_;
}
}
}
else
{
lean_object* v___x_1741_; 
lean_dec(v___x_1730_);
lean_dec(v_stx_1354_);
v___x_1741_ = lean_box(0);
v___y_1527_ = v___y_1696_;
v___y_1528_ = v___x_1729_;
v___y_1529_ = v___x_1710_;
v___y_1530_ = v___y_1698_;
v___y_1531_ = v_pkg_x3f_1702_;
v___y_1532_ = v___x_1709_;
v___y_1533_ = v___x_1708_;
v___y_1534_ = v___x_1711_;
v___y_1535_ = v___y_1699_;
v___y_1536_ = v___x_1717_;
v___y_1537_ = v___x_1712_;
v___y_1538_ = v___y_1701_;
v_wds_x3f_1539_ = v___x_1741_;
v___y_1540_ = v___y_1703_;
v___y_1541_ = v___y_1704_;
goto v___jp_1526_;
}
}
}
}
}
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1742_ = l_Lean_Syntax_getArg(v___x_1706_, v___x_1403_);
v___x_1743_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1744_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_1745_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29));
v___x_1746_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30));
lean_inc(v___x_1742_);
v___x_1747_ = l_Lean_Syntax_isOfKind(v___x_1742_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v___x_1742_);
lean_dec(v___x_1706_);
lean_dec(v_pkg_x3f_1702_);
lean_dec(v___y_1701_);
lean_dec(v___y_1699_);
lean_dec(v___y_1696_);
v___x_1748_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1749_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1354_, v___x_1748_, v___y_1703_, v___y_1704_);
lean_dec(v_stx_1354_);
return v___x_1749_;
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1750_ = l_Lean_Syntax_getArg(v___x_1742_, v___y_1698_);
lean_dec(v___x_1742_);
v___x_1751_ = l_Lean_Syntax_getArg(v___x_1706_, v___y_1698_);
lean_dec(v___x_1706_);
v___x_1752_ = l_Lean_Syntax_isNone(v___x_1751_);
if (v___x_1752_ == 0)
{
uint8_t v___x_1753_; 
lean_inc(v___x_1751_);
v___x_1753_ = l_Lean_Syntax_matchesNull(v___x_1751_, v___y_1698_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec(v___x_1751_);
lean_dec(v___x_1750_);
lean_dec(v_pkg_x3f_1702_);
lean_dec(v___y_1701_);
lean_dec(v___y_1699_);
lean_dec(v___y_1696_);
v___x_1754_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1755_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1354_, v___x_1754_, v___y_1703_, v___y_1704_);
lean_dec(v_stx_1354_);
return v___x_1755_;
}
else
{
lean_object* v_wds_x3f_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v_wds_x3f_1756_ = l_Lean_Syntax_getArg(v___x_1751_, v___x_1403_);
lean_dec(v___x_1751_);
v___x_1757_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_1756_);
v___x_1758_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v_wds_x3f_1756_);
lean_dec(v___x_1750_);
lean_dec(v_pkg_x3f_1702_);
lean_dec(v___y_1701_);
lean_dec(v___y_1699_);
lean_dec(v___y_1696_);
v___x_1759_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1760_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1354_, v___x_1759_, v___y_1703_, v___y_1704_);
lean_dec(v_stx_1354_);
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; 
lean_dec(v_stx_1354_);
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_wds_x3f_1756_);
v___y_1675_ = v___x_1746_;
v___y_1676_ = v___y_1696_;
v___y_1677_ = v___x_1750_;
v___y_1678_ = v___x_1744_;
v___y_1679_ = v_pkg_x3f_1702_;
v___y_1680_ = v___x_1743_;
v___y_1681_ = v___y_1699_;
v___y_1682_ = v___y_1701_;
v___y_1683_ = v___x_1745_;
v_wds_x3f_1684_ = v___x_1761_;
v___y_1685_ = v___y_1703_;
v___y_1686_ = v___y_1704_;
goto v___jp_1674_;
}
}
}
else
{
lean_object* v___x_1762_; 
lean_dec(v___x_1751_);
lean_dec(v_stx_1354_);
v___x_1762_ = lean_box(0);
v___y_1675_ = v___x_1746_;
v___y_1676_ = v___y_1696_;
v___y_1677_ = v___x_1750_;
v___y_1678_ = v___x_1744_;
v___y_1679_ = v_pkg_x3f_1702_;
v___y_1680_ = v___x_1743_;
v___y_1681_ = v___y_1699_;
v___y_1682_ = v___y_1701_;
v___y_1683_ = v___x_1745_;
v_wds_x3f_1684_ = v___x_1762_;
v___y_1685_ = v___y_1703_;
v___y_1686_ = v___y_1704_;
goto v___jp_1674_;
}
}
}
}
v___jp_1763_:
{
lean_object* v___x_1769_; lean_object* v_kw_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1769_ = lean_unsigned_to_nat(2u);
v_kw_1770_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1769_);
v___x_1771_ = lean_unsigned_to_nat(3u);
v___x_1772_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1771_);
v___x_1773_ = l_Lean_Syntax_isNone(v___x_1772_);
if (v___x_1773_ == 0)
{
uint8_t v___x_1774_; 
lean_inc(v___x_1772_);
v___x_1774_ = l_Lean_Syntax_matchesNull(v___x_1772_, v___y_1765_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec(v___x_1772_);
lean_dec(v_kw_1770_);
lean_dec(v_attrs_x3f_1766_);
lean_dec(v___y_1764_);
v___x_1775_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1776_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1354_, v___x_1775_, v___y_1767_, v___y_1768_);
lean_dec(v_stx_1354_);
return v___x_1776_;
}
else
{
lean_object* v_pkg_x3f_1777_; lean_object* v___x_1778_; 
v_pkg_x3f_1777_ = l_Lean_Syntax_getArg(v___x_1772_, v___x_1403_);
lean_dec(v___x_1772_);
v___x_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_pkg_x3f_1777_);
v___y_1696_ = v___y_1764_;
v___y_1697_ = v___x_1771_;
v___y_1698_ = v___y_1765_;
v___y_1699_ = v_attrs_x3f_1766_;
v___y_1700_ = v___x_1769_;
v___y_1701_ = v_kw_1770_;
v_pkg_x3f_1702_ = v___x_1778_;
v___y_1703_ = v___y_1767_;
v___y_1704_ = v___y_1768_;
goto v___jp_1695_;
}
}
else
{
lean_object* v___x_1779_; 
lean_dec(v___x_1772_);
v___x_1779_ = lean_box(0);
v___y_1696_ = v___y_1764_;
v___y_1697_ = v___x_1771_;
v___y_1698_ = v___y_1765_;
v___y_1699_ = v_attrs_x3f_1766_;
v___y_1700_ = v___x_1769_;
v___y_1701_ = v_kw_1770_;
v_pkg_x3f_1702_ = v___x_1779_;
v___y_1703_ = v___y_1767_;
v___y_1704_ = v___y_1768_;
goto v___jp_1695_;
}
}
v___jp_1780_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1784_ = lean_unsigned_to_nat(1u);
v___x_1785_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1784_);
v___x_1786_ = l_Lean_Syntax_isNone(v___x_1785_);
if (v___x_1786_ == 0)
{
uint8_t v___x_1787_; 
lean_inc(v___x_1785_);
v___x_1787_ = l_Lean_Syntax_matchesNull(v___x_1785_, v___x_1784_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_dec(v___x_1785_);
lean_dec(v_doc_x3f_1781_);
v___x_1788_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1789_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1354_, v___x_1788_, v___y_1782_, v___y_1783_);
lean_dec(v_stx_1354_);
return v___x_1789_;
}
else
{
lean_object* v_attrs_x3f_1790_; lean_object* v___x_1791_; 
v_attrs_x3f_1790_ = l_Lean_Syntax_getArg(v___x_1785_, v___x_1403_);
lean_dec(v___x_1785_);
v___x_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1791_, 0, v_attrs_x3f_1790_);
v___y_1764_ = v_doc_x3f_1781_;
v___y_1765_ = v___x_1784_;
v_attrs_x3f_1766_ = v___x_1791_;
v___y_1767_ = v___y_1782_;
v___y_1768_ = v___y_1783_;
goto v___jp_1763_;
}
}
else
{
lean_object* v___x_1792_; 
lean_dec(v___x_1785_);
v___x_1792_ = lean_box(0);
v___y_1764_ = v_doc_x3f_1781_;
v___y_1765_ = v___x_1784_;
v_attrs_x3f_1766_ = v___x_1792_;
v___y_1767_ = v___y_1782_;
v___y_1768_ = v___y_1783_;
goto v___jp_1763_;
}
}
}
v___jp_1357_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1374_ = l_Array_append___redArg(v___y_1360_, v___y_1373_);
lean_dec_ref(v___y_1373_);
lean_inc(v___y_1362_);
v___x_1375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1375_, 0, v___y_1362_);
lean_ctor_set(v___x_1375_, 1, v___y_1370_);
lean_ctor_set(v___x_1375_, 2, v___x_1374_);
lean_inc(v___y_1362_);
v___x_1376_ = l_Lean_Syntax_node4(v___y_1362_, v___y_1364_, v___y_1368_, v___y_1363_, v___y_1361_, v___x_1375_);
lean_inc(v___y_1362_);
v___x_1377_ = l_Lean_Syntax_node5(v___y_1362_, v___y_1369_, v___y_1358_, v___y_1371_, v___y_1372_, v___x_1376_, v___y_1366_);
v___x_1378_ = l_Lean_Syntax_node2(v___y_1362_, v___y_1365_, v___y_1359_, v___x_1377_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
lean_ctor_set(v___x_1379_, 1, v___y_1367_);
return v___x_1379_;
}
v___jp_1381_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1395_ = l_Array_append___redArg(v___y_1388_, v___y_1394_);
lean_dec_ref(v___y_1394_);
lean_inc(v___y_1382_);
v___x_1396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1396_, 0, v___y_1382_);
lean_ctor_set(v___x_1396_, 1, v___y_1393_);
lean_ctor_set(v___x_1396_, 2, v___x_1395_);
lean_inc(v___y_1382_);
v___x_1397_ = l_Lean_Syntax_node4(v___y_1382_, v___y_1389_, v___y_1384_, v___y_1387_, v___y_1385_, v___x_1396_);
v___x_1398_ = l_Lean_Syntax_node5(v___y_1382_, v___x_1380_, v___y_1383_, v___y_1392_, v___y_1391_, v___y_1386_, v___x_1397_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
lean_ctor_set(v___x_1399_, 1, v___y_1390_);
return v___x_1399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1(){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1807_ = l_Lean_Elab_macroAttribute;
v___x_1808_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1));
v___x_1809_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1));
v___x_1810_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl), 3, 0);
v___x_1811_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1807_, v___x_1808_, v___x_1809_, v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___boxed(lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
return v_res_1813_;
}
}
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Extensions(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_Package(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_DSL_Extensions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_Package(builtin);
}
#ifdef __cplusplus
}
#endif
