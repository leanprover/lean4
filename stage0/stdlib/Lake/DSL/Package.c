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
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed(lean_object*, lean_object*, lean_object*);
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
v___x_50_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
lean_ctor_set(v___x_50_, 2, v___x_49_);
lean_ctor_set(v___x_50_, 3, v___x_49_);
lean_ctor_set(v___x_50_, 4, v___x_48_);
lean_ctor_set(v___x_50_, 5, v___x_48_);
lean_ctor_set(v___x_50_, 6, v___x_48_);
lean_ctor_set(v___x_50_, 7, v___x_48_);
lean_ctor_set(v___x_50_, 8, v___x_48_);
lean_ctor_set(v___x_50_, 9, v___x_48_);
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
v___x_178_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msg_171_, v___y_173_);
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref(v___x_178_);
lean_inc_n(v_macroStack_177_, 2);
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
lean_dec_ref(v___y_200_);
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
lean_object* v_a_210_; lean_object* v_fileName_211_; lean_object* v_fileMap_212_; lean_object* v_currRecDepth_213_; lean_object* v_cmdPos_214_; lean_object* v_macroStack_215_; lean_object* v_quotContext_x3f_216_; lean_object* v_currMacroScope_217_; lean_object* v_snap_x3f_218_; lean_object* v_cancelTk_x3f_219_; uint8_t v_suppressElabErrors_220_; lean_object* v_ref_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
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
v_ref_221_ = l_Lean_replaceRef(v_ref_204_, v_a_210_);
lean_dec(v_a_210_);
lean_inc(v_cancelTk_x3f_219_);
lean_inc(v_snap_x3f_218_);
lean_inc(v_currMacroScope_217_);
lean_inc(v_quotContext_x3f_216_);
lean_inc(v_macroStack_215_);
lean_inc(v_cmdPos_214_);
lean_inc(v_currRecDepth_213_);
lean_inc_ref(v_fileMap_212_);
lean_inc_ref(v_fileName_211_);
v___x_222_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_222_, 0, v_fileName_211_);
lean_ctor_set(v___x_222_, 1, v_fileMap_212_);
lean_ctor_set(v___x_222_, 2, v_currRecDepth_213_);
lean_ctor_set(v___x_222_, 3, v_cmdPos_214_);
lean_ctor_set(v___x_222_, 4, v_macroStack_215_);
lean_ctor_set(v___x_222_, 5, v_quotContext_x3f_216_);
lean_ctor_set(v___x_222_, 6, v_currMacroScope_217_);
lean_ctor_set(v___x_222_, 7, v_ref_221_);
lean_ctor_set(v___x_222_, 8, v_snap_x3f_218_);
lean_ctor_set(v___x_222_, 9, v_cancelTk_x3f_219_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*10, v_suppressElabErrors_220_);
v___x_223_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_205_, v___x_222_, v___y_207_);
lean_dec_ref(v___x_222_);
return v___x_223_;
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec_ref(v_msg_205_);
v_a_224_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_209_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_209_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg___boxed(lean_object* v_ref_232_, lean_object* v_msg_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_232_, v_msg_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v_ref_232_);
return v_res_237_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4(void){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Array_mkArray0(lean_box(0));
return v___x_243_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23));
v___x_272_ = l_Lean_stringToMessageData(v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(lean_object* v_tyName_300_, lean_object* v_id_301_, lean_object* v_ty_302_, lean_object* v_config_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___x_392_; lean_object* v_whereInfo_394_; lean_object* v_fs_395_; lean_object* v_wds_x3f_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_392_ = l_Lake_PackageConfig_instConfigInfo;
v___x_425_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22));
lean_inc(v_config_303_);
v___x_426_ = l_Lean_Syntax_isOfKind(v_config_303_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v_ty_302_);
lean_dec(v_id_301_);
lean_dec(v_tyName_300_);
v___x_427_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_428_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_303_, v___x_427_, v_a_304_, v_a_305_);
lean_dec(v_config_303_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = l_Lean_Syntax_getArg(v_config_303_, v___x_429_);
lean_inc(v___x_430_);
v___x_431_ = l_Lean_Syntax_matchesNull(v___x_430_, v___x_429_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_430_);
v___x_433_ = l_Lean_Syntax_matchesNull(v___x_430_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v___x_430_);
lean_dec(v_ty_302_);
lean_dec(v_id_301_);
lean_dec(v_tyName_300_);
v___x_434_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_435_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_303_, v___x_434_, v_a_304_, v_a_305_);
lean_dec(v_config_303_);
return v___x_435_;
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_436_ = l_Lean_Syntax_getArg(v___x_430_, v___x_429_);
lean_dec(v___x_430_);
v___x_437_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26));
lean_inc(v___x_436_);
v___x_438_ = l_Lean_Syntax_isOfKind(v___x_436_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28));
lean_inc(v___x_436_);
v___x_440_ = l_Lean_Syntax_isOfKind(v___x_436_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec(v___x_436_);
lean_dec(v_ty_302_);
lean_dec(v_id_301_);
lean_dec(v_tyName_300_);
v___x_441_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_442_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_303_, v___x_441_, v_a_304_, v_a_305_);
lean_dec(v_config_303_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_443_ = l_Lean_Syntax_getArg(v___x_436_, v___x_429_);
v___x_444_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30));
lean_inc(v___x_443_);
v___x_445_ = l_Lean_Syntax_isOfKind(v___x_443_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec(v___x_443_);
lean_dec(v___x_436_);
lean_dec(v_ty_302_);
lean_dec(v_id_301_);
lean_dec(v_tyName_300_);
v___x_446_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_447_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_303_, v___x_446_, v_a_304_, v_a_305_);
lean_dec(v_config_303_);
return v___x_447_;
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_448_ = l_Lean_Syntax_getArg(v___x_443_, v___x_432_);
v___x_449_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32));
lean_inc(v___x_448_);
v___x_450_ = l_Lean_Syntax_isOfKind(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec(v___x_448_);
lean_dec(v___x_443_);
lean_dec(v___x_436_);
lean_dec(v_ty_302_);
lean_dec(v_id_301_);
lean_dec(v_tyName_300_);
v___x_451_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_452_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_303_, v___x_451_, v_a_304_, v_a_305_);
lean_dec(v_config_303_);
return v___x_452_;
}
else
{
lean_object* v_tk_453_; lean_object* v___x_454_; lean_object* v_wds_x3f_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___x_462_; uint8_t v___x_463_; 
v_tk_453_ = l_Lean_Syntax_getArg(v___x_443_, v___x_429_);
lean_dec(v___x_443_);
v___x_454_ = l_Lean_Syntax_getArg(v___x_448_, v___x_429_);
lean_dec(v___x_448_);
v___x_462_ = l_Lean_Syntax_getArg(v___x_436_, v___x_432_);
lean_dec(v___x_436_);
v___x_463_ = l_Lean_Syntax_isNone(v___x_462_);
if (v___x_463_ == 0)
{
uint8_t v___x_464_; 
lean_inc(v___x_462_);
v___x_464_ = l_Lean_Syntax_matchesNull(v___x_462_, v___x_432_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec(v___x_462_);
lean_dec(v___x_454_);
lean_dec(v_tk_453_);
lean_dec(v_ty_302_);
lean_dec(v_id_301_);
lean_dec(v_tyName_300_);
v___x_465_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_466_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_303_, v___x_465_, v_a_304_, v_a_305_);
lean_dec(v_config_303_);
return v___x_466_;
}
else
{
lean_object* v_wds_x3f_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_wds_x3f_467_ = l_Lean_Syntax_getArg(v___x_462_, v___x_429_);
lean_dec(v___x_462_);
v___x_468_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_467_);
v___x_469_ = l_Lean_Syntax_isOfKind(v_wds_x3f_467_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec(v_wds_x3f_467_);
lean_dec(v___x_454_);
lean_dec(v_tk_453_);
lean_dec(v_ty_302_);
lean_dec(v_id_301_);
lean_dec(v_tyName_300_);
v___x_470_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_471_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_303_, v___x_470_, v_a_304_, v_a_305_);
lean_dec(v_config_303_);
return v___x_471_;
}
else
{
lean_object* v___x_472_; 
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v_wds_x3f_467_);
v_wds_x3f_456_ = v___x_472_;
v___y_457_ = v_a_304_;
v___y_458_ = v_a_305_;
goto v___jp_455_;
}
}
}
else
{
lean_object* v___x_473_; 
lean_dec(v___x_462_);
v___x_473_ = lean_box(0);
v_wds_x3f_456_ = v___x_473_;
v___y_457_ = v_a_304_;
v___y_458_ = v_a_305_;
goto v___jp_455_;
}
v___jp_455_:
{
lean_object* v_fs_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v_fs_459_ = l_Lean_Syntax_getArgs(v___x_454_);
lean_dec(v___x_454_);
v___x_460_ = l_Lean_Syntax_getHeadInfo(v_tk_453_);
lean_dec(v_tk_453_);
v___x_461_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_459_);
lean_dec_ref(v_fs_459_);
v_whereInfo_394_ = v___x_460_;
v_fs_395_ = v___x_461_;
v_wds_x3f_396_ = v_wds_x3f_456_;
v___y_397_ = v___y_457_;
v___y_398_ = v___y_458_;
goto v___jp_393_;
}
}
}
}
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_474_ = l_Lean_Syntax_getArg(v___x_436_, v___x_432_);
v___x_475_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32));
lean_inc(v___x_474_);
v___x_476_ = l_Lean_Syntax_isOfKind(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v___x_474_);
lean_dec(v___x_436_);
lean_dec(v_ty_302_);
lean_dec(v_id_301_);
lean_dec(v_tyName_300_);
v___x_477_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_478_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_303_, v___x_477_, v_a_304_, v_a_305_);
lean_dec(v_config_303_);
return v___x_478_;
}
else
{
lean_object* v_tk_479_; lean_object* v___x_480_; lean_object* v_wds_x3f_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_tk_479_ = l_Lean_Syntax_getArg(v___x_436_, v___x_429_);
v___x_480_ = l_Lean_Syntax_getArg(v___x_474_, v___x_429_);
lean_dec(v___x_474_);
v___x_488_ = lean_unsigned_to_nat(2u);
v___x_489_ = l_Lean_Syntax_getArg(v___x_436_, v___x_488_);
lean_dec(v___x_436_);
v___x_490_ = l_Lean_Syntax_isNone(v___x_489_);
if (v___x_490_ == 0)
{
uint8_t v___x_491_; 
lean_inc(v___x_489_);
v___x_491_ = l_Lean_Syntax_matchesNull(v___x_489_, v___x_432_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec(v___x_489_);
lean_dec(v___x_480_);
lean_dec(v_tk_479_);
lean_dec(v_ty_302_);
lean_dec(v_id_301_);
lean_dec(v_tyName_300_);
v___x_492_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_493_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_303_, v___x_492_, v_a_304_, v_a_305_);
lean_dec(v_config_303_);
return v___x_493_;
}
else
{
lean_object* v_wds_x3f_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_wds_x3f_494_ = l_Lean_Syntax_getArg(v___x_489_, v___x_429_);
lean_dec(v___x_489_);
v___x_495_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_494_);
v___x_496_ = l_Lean_Syntax_isOfKind(v_wds_x3f_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v_wds_x3f_494_);
lean_dec(v___x_480_);
lean_dec(v_tk_479_);
lean_dec(v_ty_302_);
lean_dec(v_id_301_);
lean_dec(v_tyName_300_);
v___x_497_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_498_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_303_, v___x_497_, v_a_304_, v_a_305_);
lean_dec(v_config_303_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; 
v___x_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_499_, 0, v_wds_x3f_494_);
v_wds_x3f_482_ = v___x_499_;
v___y_483_ = v_a_304_;
v___y_484_ = v_a_305_;
goto v___jp_481_;
}
}
}
else
{
lean_object* v___x_500_; 
lean_dec(v___x_489_);
v___x_500_ = lean_box(0);
v_wds_x3f_482_ = v___x_500_;
v___y_483_ = v_a_304_;
v___y_484_ = v_a_305_;
goto v___jp_481_;
}
v___jp_481_:
{
lean_object* v_fs_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_fs_485_ = l_Lean_Syntax_getArgs(v___x_480_);
lean_dec(v___x_480_);
v___x_486_ = l_Lean_Syntax_getHeadInfo(v_tk_479_);
lean_dec(v_tk_479_);
v___x_487_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_485_);
lean_dec_ref(v_fs_485_);
v_whereInfo_394_ = v___x_486_;
v_fs_395_ = v___x_487_;
v_wds_x3f_396_ = v_wds_x3f_482_;
v___y_397_ = v___y_483_;
v___y_398_ = v___y_484_;
goto v___jp_393_;
}
}
}
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v___x_430_);
v___x_501_ = lean_box(2);
v___x_502_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
v___x_503_ = lean_box(0);
v_whereInfo_394_ = v___x_501_;
v_fs_395_ = v___x_502_;
v_wds_x3f_396_ = v___x_503_;
v___y_397_ = v_a_304_;
v___y_398_ = v_a_305_;
goto v___jp_393_;
}
}
v___jp_307_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_316_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_313_, 5);
lean_inc_ref_n(v___y_314_, 6);
lean_inc_ref_n(v___y_311_, 6);
v___x_317_ = l_Lean_Name_mkStr4(v___y_311_, v___y_314_, v___y_313_, v___x_316_);
v___x_318_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_319_ = l_Lean_Name_mkStr4(v___y_311_, v___y_314_, v___y_313_, v___x_318_);
v___x_320_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_321_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___y_310_, 8);
v___x_322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_322_, 0, v___y_310_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
lean_ctor_set(v___x_322_, 2, v___x_321_);
lean_inc_ref_n(v___x_322_, 8);
v___x_323_ = l_Lean_Syntax_node7(v___y_310_, v___x_319_, v___x_322_, v___x_322_, v___x_322_, v___x_322_, v___x_322_, v___x_322_, v___x_322_);
v___x_324_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5));
v___x_325_ = l_Lean_Name_mkStr4(v___y_311_, v___y_314_, v___y_313_, v___x_324_);
v___x_326_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6));
v___x_327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_327_, 0, v___y_310_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_329_ = l_Lean_Name_mkStr4(v___y_311_, v___y_314_, v___y_313_, v___x_328_);
v___x_330_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
lean_inc_n(v___y_312_, 2);
v___x_331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_331_, 0, v___y_312_);
lean_ctor_set(v___x_331_, 1, v___x_320_);
lean_ctor_set(v___x_331_, 2, v___x_330_);
v___x_332_ = lean_unsigned_to_nat(2u);
v___x_333_ = lean_mk_empty_array_with_capacity(v___x_332_);
v___x_334_ = lean_array_push(v___x_333_, v_id_301_);
v___x_335_ = lean_array_push(v___x_334_, v___x_331_);
v___x_336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_336_, 0, v___y_312_);
lean_ctor_set(v___x_336_, 1, v___x_329_);
lean_ctor_set(v___x_336_, 2, v___x_335_);
v___x_337_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_338_ = l_Lean_Name_mkStr4(v___y_311_, v___y_314_, v___y_313_, v___x_337_);
v___x_339_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_340_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_341_ = l_Lean_Name_mkStr4(v___y_311_, v___y_314_, v___x_339_, v___x_340_);
v___x_342_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_343_, 0, v___y_310_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = l_Lean_Syntax_node2(v___y_310_, v___x_341_, v___x_343_, v_ty_302_);
v___x_345_ = l_Lean_Syntax_node1(v___y_310_, v___x_320_, v___x_344_);
v___x_346_ = l_Lean_Syntax_node2(v___y_310_, v___x_338_, v___x_322_, v___x_345_);
v___x_347_ = l_Lean_Syntax_node5(v___y_310_, v___x_325_, v___x_327_, v___x_336_, v___x_346_, v___y_309_, v___x_322_);
v___x_348_ = l_Lean_Syntax_node2(v___y_310_, v___x_317_, v___x_323_, v___x_347_);
lean_inc(v___x_348_);
v___x_349_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_349_, 0, v___x_348_);
v___x_350_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_config_303_, v___x_348_, v___x_349_, v___y_315_, v___y_308_);
return v___x_350_;
}
v___jp_351_:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Elab_Command_getRef___redArg(v___y_359_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_363_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref(v___x_361_);
v___x_363_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_359_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_quotContext_x3f_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; 
lean_dec_ref(v___x_363_);
v_quotContext_x3f_364_ = lean_ctor_get(v___y_359_, 5);
v___x_365_ = l_Lean_mkOptionalNode(v___y_360_);
v___x_366_ = lean_unsigned_to_nat(3u);
v___x_367_ = lean_mk_empty_array_with_capacity(v___x_366_);
v___x_368_ = lean_array_push(v___x_367_, v___y_356_);
v___x_369_ = lean_array_push(v___x_368_, v___y_355_);
v___x_370_ = lean_array_push(v___x_369_, v___x_365_);
v___x_371_ = lean_box(2);
lean_inc(v___y_354_);
v___x_372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___y_354_);
lean_ctor_set(v___x_372_, 2, v___x_370_);
v___x_373_ = 0;
v___x_374_ = l_Lean_SourceInfo_fromRef(v_a_362_, v___x_373_);
lean_dec(v_a_362_);
if (lean_obj_tag(v_quotContext_x3f_364_) == 0)
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_352_);
lean_dec_ref(v___x_375_);
v___y_308_ = v___y_352_;
v___y_309_ = v___x_372_;
v___y_310_ = v___x_374_;
v___y_311_ = v___y_353_;
v___y_312_ = v___x_371_;
v___y_313_ = v___y_358_;
v___y_314_ = v___y_357_;
v___y_315_ = v___y_359_;
goto v___jp_307_;
}
else
{
v___y_308_ = v___y_352_;
v___y_309_ = v___x_372_;
v___y_310_ = v___x_374_;
v___y_311_ = v___y_353_;
v___y_312_ = v___x_371_;
v___y_313_ = v___y_358_;
v___y_314_ = v___y_357_;
v___y_315_ = v___y_359_;
goto v___jp_307_;
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v_a_362_);
lean_dec(v___y_360_);
lean_dec(v___y_356_);
lean_dec(v___y_355_);
lean_dec(v_config_303_);
lean_dec(v_ty_302_);
lean_dec(v_id_301_);
v_a_376_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_363_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_363_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v___y_360_);
lean_dec(v___y_356_);
lean_dec(v___y_355_);
lean_dec(v_config_303_);
lean_dec(v_ty_302_);
lean_dec(v_id_301_);
v_a_384_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_361_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_361_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
v___jp_393_:
{
lean_object* v_fieldMap_399_; lean_object* v___x_400_; 
v_fieldMap_399_ = lean_ctor_get(v___x_392_, 1);
v___x_400_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_300_, v_fieldMap_399_, v_fs_395_, v___y_397_, v___y_398_);
lean_dec_ref(v_fs_395_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_402_; lean_object* v_whereTk_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref(v___x_400_);
v___x_402_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13));
v_whereTk_403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_whereTk_403_, 0, v_whereInfo_394_);
lean_ctor_set(v_whereTk_403_, 1, v___x_402_);
v___x_404_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_405_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_406_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_407_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18));
if (lean_obj_tag(v_wds_x3f_396_) == 0)
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
v___y_352_ = v___y_398_;
v___y_353_ = v___x_404_;
v___y_354_ = v___x_407_;
v___y_355_ = v_a_401_;
v___y_356_ = v_whereTk_403_;
v___y_357_ = v___x_405_;
v___y_358_ = v___x_406_;
v___y_359_ = v___y_397_;
v___y_360_ = v___x_408_;
goto v___jp_351_;
}
else
{
lean_object* v_val_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
v_val_409_ = lean_ctor_get(v_wds_x3f_396_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v_wds_x3f_396_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v_wds_x3f_396_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_val_409_);
lean_dec(v_wds_x3f_396_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_val_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
v___y_352_ = v___y_398_;
v___y_353_ = v___x_404_;
v___y_354_ = v___x_407_;
v___y_355_ = v_a_401_;
v___y_356_ = v_whereTk_403_;
v___y_357_ = v___x_405_;
v___y_358_ = v___x_406_;
v___y_359_ = v___y_397_;
v___y_360_ = v___x_414_;
goto v___jp_351_;
}
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec(v_wds_x3f_396_);
lean_dec(v_whereInfo_394_);
lean_dec(v_config_303_);
lean_dec(v_ty_302_);
lean_dec(v_id_301_);
v_a_417_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_400_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_400_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___boxed(lean_object* v_tyName_504_, lean_object* v_id_505_, lean_object* v_ty_506_, lean_object* v_config_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v_tyName_504_, v_id_505_, v_ty_506_, v_config_507_, v_a_508_, v_a_509_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
return v_res_511_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19));
v___x_541_ = l_String_toRawSubstring_x27(v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33));
v___x_563_ = l_String_toRawSubstring_x27(v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39));
v___x_571_ = l_String_toRawSubstring_x27(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42));
v___x_576_ = l_String_toRawSubstring_x27(v___x_575_);
return v___x_576_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49));
v___x_585_ = l_String_toRawSubstring_x27(v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61));
v___x_606_ = l_String_toRawSubstring_x27(v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(lean_object* v_stx_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12));
lean_inc(v_stx_609_);
v___x_682_ = l_Lean_Syntax_isOfKind(v_stx_609_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
v___x_684_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_609_, v___x_683_, v_a_610_, v_a_611_);
lean_dec(v_stx_609_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; uint8_t v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; uint8_t v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v_a_819_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; uint8_t v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v_a_851_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; uint8_t v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v_a_942_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; uint8_t v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; uint8_t v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v_a_1054_; lean_object* v_kw_1082_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v_nameStx_x3f_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = l_Lean_Syntax_getArg(v_stx_609_, v___x_685_);
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = l_Lean_Syntax_getArg(v_stx_609_, v___x_687_);
v___x_689_ = lean_unsigned_to_nat(2u);
v_kw_1082_ = l_Lean_Syntax_getArg(v_stx_609_, v___x_689_);
v___x_1169_ = lean_unsigned_to_nat(3u);
v___x_1170_ = l_Lean_Syntax_getArg(v_stx_609_, v___x_1169_);
v___x_1171_ = l_Lean_Syntax_isNone(v___x_1170_);
if (v___x_1171_ == 0)
{
uint8_t v___x_1172_; 
lean_inc(v___x_1170_);
v___x_1172_ = l_Lean_Syntax_matchesNull(v___x_1170_, v___x_687_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec(v___x_1170_);
lean_dec(v_kw_1082_);
lean_dec(v___x_688_);
lean_dec(v___x_686_);
v___x_1173_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
v___x_1174_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_609_, v___x_1173_, v_a_610_, v_a_611_);
lean_dec(v_stx_609_);
return v___x_1174_;
}
else
{
lean_object* v_nameStx_x3f_1175_; lean_object* v___x_1176_; 
v_nameStx_x3f_1175_ = l_Lean_Syntax_getArg(v___x_1170_, v___x_685_);
lean_dec(v___x_1170_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_nameStx_x3f_1175_);
v_nameStx_x3f_1154_ = v___x_1176_;
v___y_1155_ = v_a_610_;
v___y_1156_ = v_a_611_;
goto v___jp_1153_;
}
}
else
{
lean_object* v___x_1177_; 
lean_dec(v___x_1170_);
v___x_1177_ = lean_box(0);
v_nameStx_x3f_1154_ = v___x_1177_;
v___y_1155_ = v_a_610_;
v___y_1156_ = v_a_611_;
goto v___jp_1153_;
}
v___jp_690_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_inc_ref_n(v___y_707_, 3);
v___x_718_ = l_Array_append___redArg(v___y_707_, v___y_717_);
lean_dec_ref(v___y_717_);
lean_inc_n(v___y_703_, 6);
lean_inc_n(v___y_709_, 18);
v___x_719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_719_, 0, v___y_709_);
lean_ctor_set(v___x_719_, 1, v___y_703_);
lean_ctor_set(v___x_719_, 2, v___x_718_);
v___x_720_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15));
lean_inc_ref(v___y_695_);
lean_inc_ref_n(v___y_692_, 6);
lean_inc_ref_n(v___y_706_, 7);
v___x_721_ = l_Lean_Name_mkStr4(v___y_706_, v___y_692_, v___y_695_, v___x_720_);
v___x_722_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16));
v___x_723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_723_, 0, v___y_709_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
lean_inc_ref(v___y_708_);
v___x_724_ = l_Lean_Syntax_SepArray_ofElems(v___y_708_, v___y_712_);
lean_dec_ref(v___y_712_);
v___x_725_ = l_Array_append___redArg(v___y_707_, v___x_724_);
lean_dec_ref(v___x_724_);
v___x_726_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_726_, 0, v___y_709_);
lean_ctor_set(v___x_726_, 1, v___y_703_);
lean_ctor_set(v___x_726_, 2, v___x_725_);
v___x_727_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17));
v___x_728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_728_, 0, v___y_709_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
lean_inc(v___x_721_);
v___x_729_ = l_Lean_Syntax_node3(v___y_709_, v___x_721_, v___x_723_, v___x_726_, v___x_728_);
v___x_730_ = l_Lean_Syntax_node1(v___y_709_, v___y_703_, v___x_729_);
v___x_731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_731_, 0, v___y_709_);
lean_ctor_set(v___x_731_, 1, v___y_703_);
lean_ctor_set(v___x_731_, 2, v___y_707_);
lean_inc_ref_n(v___x_731_, 8);
lean_inc(v___y_694_);
v___x_732_ = l_Lean_Syntax_node7(v___y_709_, v___y_694_, v___x_719_, v___x_730_, v___x_731_, v___x_731_, v___x_731_, v___x_731_, v___x_731_);
v___x_733_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18));
lean_inc_ref_n(v___y_700_, 3);
v___x_734_ = l_Lean_Name_mkStr4(v___y_706_, v___y_692_, v___y_700_, v___x_733_);
v___x_735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_735_, 0, v___y_709_);
lean_ctor_set(v___x_735_, 1, v___x_733_);
v___x_736_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_737_ = l_Lean_Name_mkStr4(v___y_706_, v___y_692_, v___y_700_, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
lean_inc_n(v___y_716_, 2);
v___x_739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_739_, 0, v___y_716_);
lean_ctor_set(v___x_739_, 1, v___y_703_);
lean_ctor_set(v___x_739_, 2, v___x_738_);
v___x_740_ = lean_mk_empty_array_with_capacity(v___x_689_);
lean_inc(v___y_693_);
lean_inc_ref(v___x_740_);
v___x_741_ = lean_array_push(v___x_740_, v___y_693_);
lean_inc_ref(v___x_739_);
v___x_742_ = lean_array_push(v___x_741_, v___x_739_);
lean_inc(v___x_737_);
v___x_743_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_743_, 0, v___y_716_);
lean_ctor_set(v___x_743_, 1, v___x_737_);
lean_ctor_set(v___x_743_, 2, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_745_ = l_Lean_Name_mkStr4(v___y_706_, v___y_692_, v___y_700_, v___x_744_);
v___x_746_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_747_ = l_Lean_Name_mkStr4(v___y_706_, v___y_692_, v___y_695_, v___x_746_);
v___x_748_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_749_, 0, v___y_709_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20);
v___x_751_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21));
v___x_752_ = l_Lean_addMacroScope(v___y_713_, v___x_751_, v___y_697_);
v___x_753_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23));
v___x_754_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24));
lean_inc(v___y_702_);
v___x_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v___y_702_);
v___x_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_753_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_757_, 0, v___y_709_);
lean_ctor_set(v___x_757_, 1, v___x_750_);
lean_ctor_set(v___x_757_, 2, v___x_752_);
lean_ctor_set(v___x_757_, 3, v___x_756_);
v___x_758_ = l_Lean_Syntax_node2(v___y_709_, v___x_747_, v___x_749_, v___x_757_);
v___x_759_ = l_Lean_Syntax_node1(v___y_709_, v___y_703_, v___x_758_);
lean_inc(v___x_745_);
v___x_760_ = l_Lean_Syntax_node2(v___y_709_, v___x_745_, v___x_731_, v___x_759_);
v___x_761_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25));
v___x_762_ = l_Lean_Name_mkStr4(v___y_706_, v___y_692_, v___y_700_, v___x_761_);
lean_inc_ref(v___y_705_);
v___x_763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_763_, 0, v___y_709_);
lean_ctor_set(v___x_763_, 1, v___y_705_);
v___x_764_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26));
v___x_765_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27));
v___x_766_ = l_Lean_Name_mkStr4(v___y_706_, v___y_692_, v___x_764_, v___x_765_);
lean_inc(v___x_766_);
v___x_767_ = l_Lean_Syntax_node2(v___y_709_, v___x_766_, v___x_731_, v___x_731_);
lean_inc(v___x_762_);
v___x_768_ = l_Lean_Syntax_node4(v___y_709_, v___x_762_, v___x_763_, v___y_710_, v___x_767_, v___x_731_);
lean_inc(v___x_734_);
v___x_769_ = l_Lean_Syntax_node4(v___y_709_, v___x_734_, v___x_735_, v___x_743_, v___x_760_, v___x_768_);
lean_inc(v___y_696_);
v___x_770_ = l_Lean_Syntax_node2(v___y_709_, v___y_696_, v___x_732_, v___x_769_);
lean_inc(v___x_770_);
v___x_771_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_771_, 0, v___x_770_);
v___x_772_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_stx_609_, v___x_770_, v___x_771_, v___y_698_, v___y_701_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v___x_773_; 
lean_dec_ref(v___x_772_);
v___x_773_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_698_, v___y_701_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_775_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref(v___x_773_);
v___x_775_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_698_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec_ref(v___x_775_);
lean_inc_ref(v___y_691_);
v___x_776_ = l_Lean_Name_str___override(v___y_711_, v___y_691_);
v___x_777_ = l_Lean_mkIdentFrom(v___y_693_, v___x_776_, v___y_715_);
lean_dec(v___y_693_);
if (lean_obj_tag(v___y_714_) == 0)
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_701_);
lean_dec_ref(v___x_778_);
v___y_614_ = v___x_745_;
v___y_615_ = v___x_722_;
v___y_616_ = v___x_766_;
v___y_617_ = v___y_704_;
v___y_618_ = v_a_774_;
v___y_619_ = v___y_705_;
v___y_620_ = v___x_762_;
v___y_621_ = v___y_707_;
v___y_622_ = v___y_706_;
v___y_623_ = v___x_737_;
v___y_624_ = v___x_740_;
v___y_625_ = v___x_777_;
v___y_626_ = v___y_694_;
v___y_627_ = v___x_734_;
v___y_628_ = v___x_733_;
v___y_629_ = v___x_721_;
v___y_630_ = v___y_696_;
v___y_631_ = v___y_698_;
v___y_632_ = v___y_699_;
v___y_633_ = v___x_727_;
v___y_634_ = v___y_701_;
v___y_635_ = v___x_739_;
v___y_636_ = v___y_716_;
v___y_637_ = v___y_703_;
goto v___jp_613_;
}
else
{
lean_dec_ref(v___y_714_);
v___y_614_ = v___x_745_;
v___y_615_ = v___x_722_;
v___y_616_ = v___x_766_;
v___y_617_ = v___y_704_;
v___y_618_ = v_a_774_;
v___y_619_ = v___y_705_;
v___y_620_ = v___x_762_;
v___y_621_ = v___y_707_;
v___y_622_ = v___y_706_;
v___y_623_ = v___x_737_;
v___y_624_ = v___x_740_;
v___y_625_ = v___x_777_;
v___y_626_ = v___y_694_;
v___y_627_ = v___x_734_;
v___y_628_ = v___x_733_;
v___y_629_ = v___x_721_;
v___y_630_ = v___y_696_;
v___y_631_ = v___y_698_;
v___y_632_ = v___y_699_;
v___y_633_ = v___x_727_;
v___y_634_ = v___y_701_;
v___y_635_ = v___x_739_;
v___y_636_ = v___y_716_;
v___y_637_ = v___y_703_;
goto v___jp_613_;
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec(v_a_774_);
lean_dec(v___x_766_);
lean_dec(v___x_762_);
lean_dec(v___x_745_);
lean_dec_ref(v___x_740_);
lean_dec_ref(v___x_739_);
lean_dec(v___x_737_);
lean_dec(v___x_734_);
lean_dec(v___x_721_);
lean_dec(v___y_716_);
lean_dec(v___y_714_);
lean_dec(v___y_711_);
lean_dec(v___y_704_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_696_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
v_a_779_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_775_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_775_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v___x_766_);
lean_dec(v___x_762_);
lean_dec(v___x_745_);
lean_dec_ref(v___x_740_);
lean_dec_ref(v___x_739_);
lean_dec(v___x_737_);
lean_dec(v___x_734_);
lean_dec(v___x_721_);
lean_dec(v___y_716_);
lean_dec(v___y_714_);
lean_dec(v___y_711_);
lean_dec(v___y_704_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_696_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
v_a_787_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_773_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_773_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_dec(v___x_766_);
lean_dec(v___x_762_);
lean_dec(v___x_745_);
lean_dec_ref(v___x_740_);
lean_dec_ref(v___x_739_);
lean_dec(v___x_737_);
lean_dec(v___x_734_);
lean_dec(v___x_721_);
lean_dec(v___y_716_);
lean_dec(v___y_714_);
lean_dec(v___y_711_);
lean_dec(v___y_704_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_696_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
return v___x_772_;
}
}
v___jp_795_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_820_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_821_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_803_, 2);
lean_inc_ref_n(v___y_800_, 2);
v___x_822_ = l_Lean_Name_mkStr4(v___y_800_, v___y_803_, v___x_820_, v___x_821_);
v___x_823_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_824_ = l_Lean_Name_mkStr4(v___y_800_, v___y_803_, v___x_820_, v___x_823_);
if (lean_obj_tag(v___y_804_) == 1)
{
lean_object* v_val_825_; lean_object* v___x_826_; 
v_val_825_ = lean_ctor_get(v___y_804_, 0);
lean_inc(v_val_825_);
lean_dec_ref(v___y_804_);
v___x_826_ = l_Array_mkArray1___redArg(v_val_825_);
v___y_691_ = v___y_796_;
v___y_692_ = v___y_803_;
v___y_693_ = v___y_807_;
v___y_694_ = v___x_824_;
v___y_695_ = v___y_809_;
v___y_696_ = v___x_822_;
v___y_697_ = v___y_810_;
v___y_698_ = v___y_811_;
v___y_699_ = v___y_812_;
v___y_700_ = v___x_820_;
v___y_701_ = v___y_813_;
v___y_702_ = v___y_817_;
v___y_703_ = v___y_818_;
v___y_704_ = v___y_797_;
v___y_705_ = v___y_798_;
v___y_706_ = v___y_800_;
v___y_707_ = v___y_799_;
v___y_708_ = v___y_801_;
v___y_709_ = v___y_802_;
v___y_710_ = v___y_806_;
v___y_711_ = v___y_805_;
v___y_712_ = v___y_808_;
v___y_713_ = v_a_819_;
v___y_714_ = v___y_814_;
v___y_715_ = v___y_815_;
v___y_716_ = v___y_816_;
v___y_717_ = v___x_826_;
goto v___jp_690_;
}
else
{
lean_object* v___x_827_; 
lean_dec(v___y_804_);
v___x_827_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___y_691_ = v___y_796_;
v___y_692_ = v___y_803_;
v___y_693_ = v___y_807_;
v___y_694_ = v___x_824_;
v___y_695_ = v___y_809_;
v___y_696_ = v___x_822_;
v___y_697_ = v___y_810_;
v___y_698_ = v___y_811_;
v___y_699_ = v___y_812_;
v___y_700_ = v___x_820_;
v___y_701_ = v___y_813_;
v___y_702_ = v___y_817_;
v___y_703_ = v___y_818_;
v___y_704_ = v___y_797_;
v___y_705_ = v___y_798_;
v___y_706_ = v___y_800_;
v___y_707_ = v___y_799_;
v___y_708_ = v___y_801_;
v___y_709_ = v___y_802_;
v___y_710_ = v___y_806_;
v___y_711_ = v___y_805_;
v___y_712_ = v___y_808_;
v___y_713_ = v_a_819_;
v___y_714_ = v___y_814_;
v___y_715_ = v___y_815_;
v___y_716_ = v___y_816_;
v___y_717_ = v___x_827_;
goto v___jp_690_;
}
}
v___jp_828_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_852_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
lean_inc_ref_n(v___y_841_, 6);
lean_inc_ref_n(v___y_834_, 6);
lean_inc_ref_n(v___y_832_, 6);
v___x_853_ = l_Lean_Name_mkStr4(v___y_832_, v___y_834_, v___y_841_, v___x_852_);
v___x_854_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
lean_inc_n(v___y_830_, 23);
v___x_855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_855_, 0, v___y_830_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
lean_inc_ref(v___y_833_);
lean_inc_n(v___y_850_, 5);
v___x_856_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_856_, 0, v___y_830_);
lean_ctor_set(v___x_856_, 1, v___y_850_);
lean_ctor_set(v___x_856_, 2, v___y_833_);
v___x_857_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31));
v___x_858_ = l_Lean_Name_mkStr4(v___y_832_, v___y_834_, v___y_841_, v___x_857_);
v___x_859_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31));
v___x_860_ = l_Lean_Name_mkStr4(v___y_832_, v___y_834_, v___y_841_, v___x_859_);
v___x_861_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32));
v___x_862_ = l_Lean_Name_mkStr4(v___y_832_, v___y_834_, v___y_841_, v___x_861_);
v___x_863_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33));
v___x_864_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34);
v___x_865_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35));
lean_inc_n(v___y_838_, 2);
lean_inc_n(v_a_851_, 2);
v___x_866_ = l_Lean_addMacroScope(v_a_851_, v___x_865_, v___y_838_);
lean_inc_n(v___y_849_, 3);
v___x_867_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_867_, 0, v___y_830_);
lean_ctor_set(v___x_867_, 1, v___x_864_);
lean_ctor_set(v___x_867_, 2, v___x_866_);
lean_ctor_set(v___x_867_, 3, v___y_849_);
lean_inc_ref_n(v___x_856_, 14);
lean_inc_n(v___x_862_, 2);
v___x_868_ = l_Lean_Syntax_node2(v___y_830_, v___x_862_, v___x_867_, v___x_856_);
v___x_869_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36));
v___x_870_ = l_Lean_Name_mkStr4(v___y_832_, v___y_834_, v___y_841_, v___x_869_);
v___x_871_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37));
v___x_872_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_872_, 0, v___y_830_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
lean_inc_ref_n(v___x_872_, 2);
lean_inc_n(v___x_870_, 2);
v___x_873_ = l_Lean_Syntax_node3(v___y_830_, v___x_870_, v___x_872_, v___x_856_, v___y_845_);
v___x_874_ = l_Lean_Syntax_node3(v___y_830_, v___y_850_, v___x_856_, v___x_856_, v___x_873_);
lean_inc_n(v___x_860_, 2);
v___x_875_ = l_Lean_Syntax_node2(v___y_830_, v___x_860_, v___x_868_, v___x_874_);
v___x_876_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38));
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___y_830_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40);
v___x_879_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41));
v___x_880_ = l_Lean_addMacroScope(v_a_851_, v___x_879_, v___y_838_);
v___x_881_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_881_, 0, v___y_830_);
lean_ctor_set(v___x_881_, 1, v___x_878_);
lean_ctor_set(v___x_881_, 2, v___x_880_);
lean_ctor_set(v___x_881_, 3, v___y_849_);
v___x_882_ = l_Lean_Syntax_node2(v___y_830_, v___x_862_, v___x_881_, v___x_856_);
v___x_883_ = l_Lean_Syntax_node3(v___y_830_, v___x_870_, v___x_872_, v___x_856_, v___y_829_);
v___x_884_ = l_Lean_Syntax_node3(v___y_830_, v___y_850_, v___x_856_, v___x_856_, v___x_883_);
v___x_885_ = l_Lean_Syntax_node2(v___y_830_, v___x_860_, v___x_882_, v___x_884_);
v___x_886_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43);
v___x_887_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44));
v___x_888_ = l_Lean_addMacroScope(v_a_851_, v___x_887_, v___y_838_);
v___x_889_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_889_, 0, v___y_830_);
lean_ctor_set(v___x_889_, 1, v___x_886_);
lean_ctor_set(v___x_889_, 2, v___x_888_);
lean_ctor_set(v___x_889_, 3, v___y_849_);
v___x_890_ = l_Lean_Syntax_node2(v___y_830_, v___x_862_, v___x_889_, v___x_856_);
v___x_891_ = l_Lean_Syntax_node3(v___y_830_, v___x_870_, v___x_872_, v___x_856_, v___y_835_);
v___x_892_ = l_Lean_Syntax_node3(v___y_830_, v___y_850_, v___x_856_, v___x_856_, v___x_891_);
v___x_893_ = l_Lean_Syntax_node2(v___y_830_, v___x_860_, v___x_890_, v___x_892_);
lean_inc_ref(v___x_877_);
v___x_894_ = l_Lean_Syntax_node5(v___y_830_, v___y_850_, v___x_875_, v___x_877_, v___x_885_, v___x_877_, v___x_893_);
v___x_895_ = l_Lean_Syntax_node1(v___y_830_, v___x_858_, v___x_894_);
v___x_896_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45));
v___x_897_ = l_Lean_Name_mkStr4(v___y_832_, v___y_834_, v___y_841_, v___x_896_);
v___x_898_ = l_Lean_Syntax_node1(v___y_830_, v___x_897_, v___x_856_);
v___x_899_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46));
v___x_900_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_900_, 0, v___y_830_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l_Lean_Syntax_node6(v___y_830_, v___x_853_, v___x_855_, v___x_856_, v___x_895_, v___x_898_, v___x_856_, v___x_900_);
v___x_902_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_842_, v___y_844_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_904_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v___x_902_);
v___x_904_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_842_);
if (lean_obj_tag(v___x_904_) == 0)
{
if (lean_obj_tag(v___y_846_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v_a_907_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref(v___x_904_);
v___x_906_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_844_);
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref(v___x_906_);
v___y_796_ = v___x_863_;
v___y_797_ = v___y_831_;
v___y_798_ = v___x_871_;
v___y_799_ = v___y_833_;
v___y_800_ = v___y_832_;
v___y_801_ = v___x_876_;
v___y_802_ = v_a_903_;
v___y_803_ = v___y_834_;
v___y_804_ = v___y_837_;
v___y_805_ = v___y_836_;
v___y_806_ = v___x_901_;
v___y_807_ = v___y_839_;
v___y_808_ = v___y_840_;
v___y_809_ = v___y_841_;
v___y_810_ = v_a_905_;
v___y_811_ = v___y_842_;
v___y_812_ = v___y_843_;
v___y_813_ = v___y_844_;
v___y_814_ = v___y_846_;
v___y_815_ = v___y_847_;
v___y_816_ = v___y_848_;
v___y_817_ = v___y_849_;
v___y_818_ = v___y_850_;
v_a_819_ = v_a_907_;
goto v___jp_795_;
}
else
{
lean_object* v_a_908_; lean_object* v_val_909_; 
v_a_908_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_908_);
lean_dec_ref(v___x_904_);
v_val_909_ = lean_ctor_get(v___y_846_, 0);
lean_inc(v_val_909_);
v___y_796_ = v___x_863_;
v___y_797_ = v___y_831_;
v___y_798_ = v___x_871_;
v___y_799_ = v___y_833_;
v___y_800_ = v___y_832_;
v___y_801_ = v___x_876_;
v___y_802_ = v_a_903_;
v___y_803_ = v___y_834_;
v___y_804_ = v___y_837_;
v___y_805_ = v___y_836_;
v___y_806_ = v___x_901_;
v___y_807_ = v___y_839_;
v___y_808_ = v___y_840_;
v___y_809_ = v___y_841_;
v___y_810_ = v_a_908_;
v___y_811_ = v___y_842_;
v___y_812_ = v___y_843_;
v___y_813_ = v___y_844_;
v___y_814_ = v___y_846_;
v___y_815_ = v___y_847_;
v___y_816_ = v___y_848_;
v___y_817_ = v___y_849_;
v___y_818_ = v___y_850_;
v_a_819_ = v_val_909_;
goto v___jp_795_;
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v_a_903_);
lean_dec(v___x_901_);
lean_dec(v___y_848_);
lean_dec(v___y_846_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_831_);
lean_dec(v_stx_609_);
v_a_910_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_904_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_904_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v___x_901_);
lean_dec(v___y_848_);
lean_dec(v___y_846_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_831_);
lean_dec(v_stx_609_);
v_a_918_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_902_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_902_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
v___jp_926_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_943_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_944_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_945_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47));
lean_inc_ref_n(v___y_928_, 2);
v___x_946_ = l_Lean_Name_mkStr4(v___y_928_, v___x_943_, v___x_944_, v___x_945_);
v___x_947_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48));
v___x_948_ = l_Lean_Name_mkStr4(v___y_928_, v___x_943_, v___x_944_, v___x_947_);
v___x_949_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_950_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___y_940_, 2);
v___x_951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_951_, 0, v___y_940_);
lean_ctor_set(v___x_951_, 1, v___x_949_);
lean_ctor_set(v___x_951_, 2, v___x_950_);
lean_inc_ref(v___x_951_);
lean_inc(v___x_948_);
v___x_952_ = l_Lean_Syntax_node1(v___y_940_, v___x_948_, v___x_951_);
v___x_953_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref(v___x_953_);
v___x_955_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_932_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref(v___x_955_);
v___x_957_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50);
v___x_958_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52));
v___x_959_ = l_Lean_addMacroScope(v_a_942_, v___x_958_, v___y_929_);
lean_inc(v___y_939_);
lean_inc_n(v___y_940_, 2);
v___x_960_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_960_, 0, v___y_940_);
lean_ctor_set(v___x_960_, 1, v___x_957_);
lean_ctor_set(v___x_960_, 2, v___x_959_);
lean_ctor_set(v___x_960_, 3, v___y_939_);
v___x_961_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53));
v___x_962_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54));
lean_inc_ref(v___y_928_);
v___x_963_ = l_Lean_Name_mkStr4(v___y_928_, v___x_943_, v___x_961_, v___x_962_);
v___x_964_ = l_Lean_Syntax_node2(v___y_940_, v___x_963_, v___x_960_, v___x_951_);
lean_inc(v___x_946_);
v___x_965_ = l_Lean_Syntax_node2(v___y_940_, v___x_946_, v___x_952_, v___x_964_);
v___x_966_ = lean_mk_empty_array_with_capacity(v___x_687_);
v___x_967_ = lean_array_push(v___x_966_, v___x_965_);
v___x_968_ = l_Lake_DSL_expandAttrs(v___y_941_);
v___x_969_ = l_Array_append___redArg(v___x_967_, v___x_968_);
lean_dec_ref(v___x_968_);
v___x_970_ = l_Lake_DSL_packageDeclName;
v___x_971_ = l_Lean_mkIdentFrom(v___y_936_, v___x_970_, v___y_937_);
lean_dec(v___y_936_);
if (lean_obj_tag(v___y_935_) == 0)
{
lean_object* v___x_972_; lean_object* v_a_973_; 
v___x_972_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_933_);
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref(v___x_972_);
v___y_829_ = v___y_927_;
v___y_830_ = v_a_954_;
v___y_831_ = v___x_946_;
v___y_832_ = v___y_928_;
v___y_833_ = v___x_950_;
v___y_834_ = v___x_943_;
v___y_835_ = v___y_930_;
v___y_836_ = v___x_970_;
v___y_837_ = v___y_931_;
v___y_838_ = v_a_956_;
v___y_839_ = v___x_971_;
v___y_840_ = v___x_969_;
v___y_841_ = v___x_944_;
v___y_842_ = v___y_932_;
v___y_843_ = v___x_948_;
v___y_844_ = v___y_933_;
v___y_845_ = v___y_934_;
v___y_846_ = v___y_935_;
v___y_847_ = v___y_937_;
v___y_848_ = v___y_938_;
v___y_849_ = v___y_939_;
v___y_850_ = v___x_949_;
v_a_851_ = v_a_973_;
goto v___jp_828_;
}
else
{
lean_object* v_val_974_; 
v_val_974_ = lean_ctor_get(v___y_935_, 0);
lean_inc(v_val_974_);
v___y_829_ = v___y_927_;
v___y_830_ = v_a_954_;
v___y_831_ = v___x_946_;
v___y_832_ = v___y_928_;
v___y_833_ = v___x_950_;
v___y_834_ = v___x_943_;
v___y_835_ = v___y_930_;
v___y_836_ = v___x_970_;
v___y_837_ = v___y_931_;
v___y_838_ = v_a_956_;
v___y_839_ = v___x_971_;
v___y_840_ = v___x_969_;
v___y_841_ = v___x_944_;
v___y_842_ = v___y_932_;
v___y_843_ = v___x_948_;
v___y_844_ = v___y_933_;
v___y_845_ = v___y_934_;
v___y_846_ = v___y_935_;
v___y_847_ = v___y_937_;
v___y_848_ = v___y_938_;
v___y_849_ = v___y_939_;
v___y_850_ = v___x_949_;
v_a_851_ = v_val_974_;
goto v___jp_828_;
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_a_954_);
lean_dec(v___x_952_);
lean_dec_ref(v___x_951_);
lean_dec(v___x_948_);
lean_dec(v___x_946_);
lean_dec(v_a_942_);
lean_dec(v___y_941_);
lean_dec(v___y_940_);
lean_dec(v___y_938_);
lean_dec(v___y_936_);
lean_dec(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec(v___y_930_);
lean_dec(v___y_929_);
lean_dec(v___y_927_);
lean_dec(v_stx_609_);
v_a_975_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_955_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_955_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v___x_952_);
lean_dec_ref(v___x_951_);
lean_dec(v___x_948_);
lean_dec(v___x_946_);
lean_dec(v_a_942_);
lean_dec(v___y_941_);
lean_dec(v___y_940_);
lean_dec(v___y_938_);
lean_dec(v___y_936_);
lean_dec(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec(v___y_930_);
lean_dec(v___y_929_);
lean_dec(v___y_927_);
lean_dec(v_stx_609_);
v_a_983_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_953_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_953_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
v___jp_991_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1005_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1006_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57));
v___x_1007_ = l_Nat_reprFast(v___y_997_);
v___x_1008_ = lean_box(2);
v___x_1009_ = l_Lean_Syntax_mkNumLit(v___x_1007_, v___x_1008_);
v___x_1010_ = lean_mk_empty_array_with_capacity(v___x_689_);
lean_inc_ref(v___x_1010_);
v___x_1011_ = lean_array_push(v___x_1010_, v___y_1004_);
v___x_1012_ = lean_array_push(v___x_1011_, v___x_1009_);
v___x_1013_ = l_Lean_Syntax_mkCApp(v___x_1006_, v___x_1012_);
v___x_1014_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59));
lean_inc(v___x_1013_);
v___x_1015_ = lean_array_push(v___x_1010_, v___x_1013_);
lean_inc(v___y_992_);
v___x_1016_ = lean_array_push(v___x_1015_, v___y_992_);
v___x_1017_ = l_Lean_Syntax_mkCApp(v___x_1014_, v___x_1016_);
lean_inc(v___y_993_);
v___x_1018_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v___x_1014_, v___y_993_, v___x_1017_, v___y_1001_, v___y_995_, v___y_996_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v___x_1019_; 
lean_dec_ref(v___x_1018_);
v___x_1019_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_995_, v___y_996_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1021_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref(v___x_1019_);
v___x_1021_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_995_);
if (lean_obj_tag(v___x_1021_) == 0)
{
if (lean_obj_tag(v___y_998_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v_a_1024_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_996_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref(v___x_1023_);
v___y_927_ = v___y_992_;
v___y_928_ = v___x_1005_;
v___y_929_ = v_a_1022_;
v___y_930_ = v___y_993_;
v___y_931_ = v___y_994_;
v___y_932_ = v___y_995_;
v___y_933_ = v___y_996_;
v___y_934_ = v___x_1013_;
v___y_935_ = v___y_998_;
v___y_936_ = v___y_999_;
v___y_937_ = v___y_1000_;
v___y_938_ = v___x_1008_;
v___y_939_ = v___y_1002_;
v___y_940_ = v_a_1020_;
v___y_941_ = v___y_1003_;
v_a_942_ = v_a_1024_;
goto v___jp_926_;
}
else
{
lean_object* v_a_1025_; lean_object* v_val_1026_; 
v_a_1025_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1025_);
lean_dec_ref(v___x_1021_);
v_val_1026_ = lean_ctor_get(v___y_998_, 0);
lean_inc(v_val_1026_);
v___y_927_ = v___y_992_;
v___y_928_ = v___x_1005_;
v___y_929_ = v_a_1025_;
v___y_930_ = v___y_993_;
v___y_931_ = v___y_994_;
v___y_932_ = v___y_995_;
v___y_933_ = v___y_996_;
v___y_934_ = v___x_1013_;
v___y_935_ = v___y_998_;
v___y_936_ = v___y_999_;
v___y_937_ = v___y_1000_;
v___y_938_ = v___x_1008_;
v___y_939_ = v___y_1002_;
v___y_940_ = v_a_1020_;
v___y_941_ = v___y_1003_;
v_a_942_ = v_val_1026_;
goto v___jp_926_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_a_1020_);
lean_dec(v___x_1013_);
lean_dec(v___y_1003_);
lean_dec(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec(v___y_993_);
lean_dec(v___y_992_);
lean_dec(v_stx_609_);
v_a_1027_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1021_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1021_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v___x_1013_);
lean_dec(v___y_1003_);
lean_dec(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec(v___y_993_);
lean_dec(v___y_992_);
lean_dec(v_stx_609_);
v_a_1035_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1019_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1019_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_dec(v___x_1013_);
lean_dec(v___y_1003_);
lean_dec(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec(v___y_993_);
lean_dec(v___y_992_);
lean_dec(v_stx_609_);
return v___x_1018_;
}
}
v___jp_1043_:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lake_DSL_mkConfigDeclIdent(v___y_1050_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1057_; lean_object* v_env_1058_; lean_object* v___x_1059_; lean_object* v_asyncMode_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_fst_1064_; lean_object* v_snd_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc_n(v_a_1056_, 2);
lean_dec_ref(v___x_1055_);
v___x_1057_ = lean_st_ref_get(v___y_1047_);
v_env_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc_ref(v_env_1058_);
lean_dec(v___x_1057_);
v___x_1059_ = l_Lake_nameExt;
v_asyncMode_1060_ = lean_ctor_get(v___x_1059_, 2);
v___x_1061_ = lean_box(0);
v___x_1062_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60));
v___x_1063_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1062_, v___x_1059_, v_env_1058_, v_asyncMode_1060_, v___x_1061_);
v_fst_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_fst_1064_);
v_snd_1065_ = lean_ctor_get(v___x_1063_, 1);
lean_inc(v_snd_1065_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62);
v___x_1067_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63));
v___x_1068_ = l_Lean_addMacroScope(v_a_1054_, v___x_1067_, v___y_1044_);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1070_, 0, v___y_1045_);
lean_ctor_set(v___x_1070_, 1, v___x_1066_);
lean_ctor_set(v___x_1070_, 2, v___x_1068_);
lean_ctor_set(v___x_1070_, 3, v___x_1069_);
v___x_1071_ = l_Lean_TSyntax_getId(v_a_1056_);
v___x_1072_ = l_Lake_Name_quoteFrom(v_a_1056_, v___x_1071_, v___y_1051_);
if (lean_obj_tag(v_snd_1065_) == 0)
{
lean_inc(v___x_1072_);
v___y_992_ = v___x_1072_;
v___y_993_ = v___x_1070_;
v___y_994_ = v___y_1049_;
v___y_995_ = v___y_1046_;
v___y_996_ = v___y_1047_;
v___y_997_ = v_fst_1064_;
v___y_998_ = v___y_1048_;
v___y_999_ = v_a_1056_;
v___y_1000_ = v___y_1051_;
v___y_1001_ = v___y_1052_;
v___y_1002_ = v___x_1069_;
v___y_1003_ = v___y_1053_;
v___y_1004_ = v___x_1072_;
goto v___jp_991_;
}
else
{
lean_object* v___x_1073_; 
lean_inc(v_a_1056_);
v___x_1073_ = l_Lake_Name_quoteFrom(v_a_1056_, v_snd_1065_, v___y_1051_);
v___y_992_ = v___x_1072_;
v___y_993_ = v___x_1070_;
v___y_994_ = v___y_1049_;
v___y_995_ = v___y_1046_;
v___y_996_ = v___y_1047_;
v___y_997_ = v_fst_1064_;
v___y_998_ = v___y_1048_;
v___y_999_ = v_a_1056_;
v___y_1000_ = v___y_1051_;
v___y_1001_ = v___y_1052_;
v___y_1002_ = v___x_1069_;
v___y_1003_ = v___y_1053_;
v___y_1004_ = v___x_1073_;
goto v___jp_991_;
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec(v_a_1054_);
lean_dec(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec(v_stx_609_);
v_a_1074_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1055_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1055_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
v___jp_1083_:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Elab_Command_getRef___redArg(v___y_1084_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v_fileName_1092_; lean_object* v_fileMap_1093_; lean_object* v_currRecDepth_1094_; lean_object* v_cmdPos_1095_; lean_object* v_macroStack_1096_; lean_object* v_quotContext_x3f_1097_; lean_object* v_currMacroScope_1098_; lean_object* v_snap_x3f_1099_; lean_object* v_cancelTk_x3f_1100_; uint8_t v_suppressElabErrors_1101_; lean_object* v_ref_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref(v___x_1090_);
v_fileName_1092_ = lean_ctor_get(v___y_1084_, 0);
v_fileMap_1093_ = lean_ctor_get(v___y_1084_, 1);
v_currRecDepth_1094_ = lean_ctor_get(v___y_1084_, 2);
v_cmdPos_1095_ = lean_ctor_get(v___y_1084_, 3);
v_macroStack_1096_ = lean_ctor_get(v___y_1084_, 4);
v_quotContext_x3f_1097_ = lean_ctor_get(v___y_1084_, 5);
v_currMacroScope_1098_ = lean_ctor_get(v___y_1084_, 6);
v_snap_x3f_1099_ = lean_ctor_get(v___y_1084_, 8);
v_cancelTk_x3f_1100_ = lean_ctor_get(v___y_1084_, 9);
v_suppressElabErrors_1101_ = lean_ctor_get_uint8(v___y_1084_, sizeof(void*)*10);
v_ref_1102_ = l_Lean_replaceRef(v_kw_1082_, v_a_1091_);
lean_dec(v_a_1091_);
lean_dec(v_kw_1082_);
lean_inc(v_cancelTk_x3f_1100_);
lean_inc(v_snap_x3f_1099_);
lean_inc(v_currMacroScope_1098_);
lean_inc(v_quotContext_x3f_1097_);
lean_inc(v_macroStack_1096_);
lean_inc(v_cmdPos_1095_);
lean_inc(v_currRecDepth_1094_);
lean_inc_ref(v_fileMap_1093_);
lean_inc_ref(v_fileName_1092_);
v___x_1103_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1103_, 0, v_fileName_1092_);
lean_ctor_set(v___x_1103_, 1, v_fileMap_1093_);
lean_ctor_set(v___x_1103_, 2, v_currRecDepth_1094_);
lean_ctor_set(v___x_1103_, 3, v_cmdPos_1095_);
lean_ctor_set(v___x_1103_, 4, v_macroStack_1096_);
lean_ctor_set(v___x_1103_, 5, v_quotContext_x3f_1097_);
lean_ctor_set(v___x_1103_, 6, v_currMacroScope_1098_);
lean_ctor_set(v___x_1103_, 7, v_ref_1102_);
lean_ctor_set(v___x_1103_, 8, v_snap_x3f_1099_);
lean_ctor_set(v___x_1103_, 9, v_cancelTk_x3f_1100_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*10, v_suppressElabErrors_1101_);
v___x_1104_ = l_Lean_Elab_Command_getRef___redArg(v___x_1103_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1106_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref(v___x_1104_);
v___x_1106_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1103_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; uint8_t v___x_1108_; lean_object* v___x_1109_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref(v___x_1106_);
v___x_1108_ = 0;
v___x_1109_ = l_Lean_SourceInfo_fromRef(v_a_1105_, v___x_1108_);
lean_dec(v_a_1105_);
if (lean_obj_tag(v_quotContext_x3f_1097_) == 0)
{
lean_object* v___x_1110_; lean_object* v_a_1111_; 
v___x_1110_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1085_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref(v___x_1110_);
v___y_1044_ = v_a_1107_;
v___y_1045_ = v___x_1109_;
v___y_1046_ = v___x_1103_;
v___y_1047_ = v___y_1085_;
v___y_1048_ = v_quotContext_x3f_1097_;
v___y_1049_ = v___y_1089_;
v___y_1050_ = v___y_1086_;
v___y_1051_ = v___x_1108_;
v___y_1052_ = v___y_1087_;
v___y_1053_ = v___y_1088_;
v_a_1054_ = v_a_1111_;
goto v___jp_1043_;
}
else
{
lean_object* v_val_1112_; 
v_val_1112_ = lean_ctor_get(v_quotContext_x3f_1097_, 0);
lean_inc(v_val_1112_);
lean_inc_ref(v_quotContext_x3f_1097_);
v___y_1044_ = v_a_1107_;
v___y_1045_ = v___x_1109_;
v___y_1046_ = v___x_1103_;
v___y_1047_ = v___y_1085_;
v___y_1048_ = v_quotContext_x3f_1097_;
v___y_1049_ = v___y_1089_;
v___y_1050_ = v___y_1086_;
v___y_1051_ = v___x_1108_;
v___y_1052_ = v___y_1087_;
v___y_1053_ = v___y_1088_;
v_a_1054_ = v_val_1112_;
goto v___jp_1043_;
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_a_1105_);
lean_dec_ref(v___x_1103_);
lean_dec(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec(v_stx_609_);
v_a_1113_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1106_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1106_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec_ref(v___x_1103_);
lean_dec(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec(v_stx_609_);
v_a_1121_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1104_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1104_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec(v_kw_1082_);
lean_dec(v_stx_609_);
v_a_1129_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1090_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1090_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
v___jp_1137_:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Syntax_getOptional_x3f(v___x_686_);
lean_dec(v___x_686_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_box(0);
v___y_1084_ = v___y_1138_;
v___y_1085_ = v___y_1139_;
v___y_1086_ = v___y_1140_;
v___y_1087_ = v___y_1141_;
v___y_1088_ = v___y_1142_;
v___y_1089_ = v___x_1144_;
goto v___jp_1083_;
}
else
{
lean_object* v_val_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
v_val_1145_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1143_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_val_1145_);
lean_dec(v___x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_val_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
v___y_1084_ = v___y_1138_;
v___y_1085_ = v___y_1139_;
v___y_1086_ = v___y_1140_;
v___y_1087_ = v___y_1141_;
v___y_1088_ = v___y_1142_;
v___y_1089_ = v___x_1150_;
goto v___jp_1083_;
}
}
}
}
v___jp_1153_:
{
lean_object* v___x_1157_; lean_object* v_cfg_1158_; lean_object* v___x_1159_; 
v___x_1157_ = lean_unsigned_to_nat(4u);
v_cfg_1158_ = l_Lean_Syntax_getArg(v_stx_609_, v___x_1157_);
v___x_1159_ = l_Lean_Syntax_getOptional_x3f(v___x_688_);
lean_dec(v___x_688_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_box(0);
v___y_1138_ = v___y_1155_;
v___y_1139_ = v___y_1156_;
v___y_1140_ = v_nameStx_x3f_1154_;
v___y_1141_ = v_cfg_1158_;
v___y_1142_ = v___x_1160_;
goto v___jp_1137_;
}
else
{
lean_object* v_val_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
v_val_1161_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1159_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_val_1161_);
lean_dec(v___x_1159_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_val_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
v___y_1138_ = v___y_1155_;
v___y_1139_ = v___y_1156_;
v___y_1140_ = v_nameStx_x3f_1154_;
v___y_1141_ = v_cfg_1158_;
v___y_1142_ = v___x_1166_;
goto v___jp_1137_;
}
}
}
}
}
v___jp_613_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
lean_inc_ref(v___y_621_);
lean_inc_n(v___y_637_, 5);
lean_inc_n(v___y_618_, 28);
v___x_638_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_638_, 0, v___y_618_);
lean_ctor_set(v___x_638_, 1, v___y_637_);
lean_ctor_set(v___x_638_, 2, v___y_621_);
lean_inc_ref(v___y_615_);
v___x_639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_639_, 0, v___y_618_);
lean_ctor_set(v___x_639_, 1, v___y_615_);
lean_inc_ref_n(v___x_638_, 12);
v___x_640_ = l_Lean_Syntax_node1(v___y_618_, v___y_632_, v___x_638_);
v___x_641_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0));
lean_inc_ref(v___y_622_);
v___x_642_ = l_Lean_Name_mkStr2(v___y_622_, v___x_641_);
v___x_643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_643_, 0, v___y_618_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
v___x_644_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2));
v___x_645_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3));
v___x_646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_646_, 0, v___y_618_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = l_Lean_Syntax_node1(v___y_618_, v___x_644_, v___x_646_);
v___x_648_ = l_Lean_Syntax_node1(v___y_618_, v___y_637_, v___x_647_);
v___x_649_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4));
v___x_650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_650_, 0, v___y_618_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5));
v___x_652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_652_, 0, v___y_618_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
lean_inc_ref(v___y_619_);
v___x_653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_653_, 0, v___y_618_);
lean_ctor_set(v___x_653_, 1, v___y_619_);
v___x_654_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6));
v___x_655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_655_, 0, v___y_618_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = l_Lean_Syntax_node1(v___y_618_, v___x_644_, v___x_655_);
v___x_657_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7));
v___x_658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_658_, 0, v___y_618_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
lean_inc_ref(v___x_653_);
v___x_659_ = l_Lean_Syntax_node5(v___y_618_, v___y_637_, v___x_650_, v___x_652_, v___x_653_, v___x_656_, v___x_658_);
v___x_660_ = l_Lean_Syntax_node4(v___y_618_, v___x_642_, v___x_643_, v___x_638_, v___x_648_, v___x_659_);
v___x_661_ = l_Lean_Syntax_node2(v___y_618_, v___y_617_, v___x_640_, v___x_660_);
v___x_662_ = l_Lean_Syntax_node1(v___y_618_, v___y_637_, v___x_661_);
lean_inc_ref(v___y_633_);
v___x_663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_663_, 0, v___y_618_);
lean_ctor_set(v___x_663_, 1, v___y_633_);
v___x_664_ = l_Lean_Syntax_node3(v___y_618_, v___y_629_, v___x_639_, v___x_662_, v___x_663_);
v___x_665_ = l_Lean_Syntax_node1(v___y_618_, v___y_637_, v___x_664_);
v___x_666_ = l_Lean_Syntax_node7(v___y_618_, v___y_626_, v___x_638_, v___x_665_, v___x_638_, v___x_638_, v___x_638_, v___x_638_, v___x_638_);
v___x_667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_667_, 0, v___y_618_);
lean_ctor_set(v___x_667_, 1, v___y_628_);
v___x_668_ = lean_array_push(v___y_624_, v___y_625_);
v___x_669_ = lean_array_push(v___x_668_, v___y_635_);
v___x_670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_670_, 0, v___y_636_);
lean_ctor_set(v___x_670_, 1, v___y_623_);
lean_ctor_set(v___x_670_, 2, v___x_669_);
v___x_671_ = l_Lean_Syntax_node2(v___y_618_, v___y_614_, v___x_638_, v___x_638_);
v___x_672_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9));
v___x_673_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10));
v___x_674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_674_, 0, v___y_618_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = l_Lean_Syntax_node1(v___y_618_, v___x_672_, v___x_674_);
v___x_676_ = l_Lean_Syntax_node2(v___y_618_, v___y_616_, v___x_638_, v___x_638_);
v___x_677_ = l_Lean_Syntax_node4(v___y_618_, v___y_620_, v___x_653_, v___x_675_, v___x_676_, v___x_638_);
v___x_678_ = l_Lean_Syntax_node4(v___y_618_, v___y_627_, v___x_667_, v___x_670_, v___x_671_, v___x_677_);
v___x_679_ = l_Lean_Syntax_node2(v___y_618_, v___y_630_, v___x_666_, v___x_678_);
v___x_680_ = l_Lean_Elab_Command_elabCommand(v___x_679_, v___y_631_, v___y_634_);
lean_dec_ref(v___y_631_);
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed(lean_object* v_stx_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(v_stx_1178_, v_a_1179_, v_a_1180_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(lean_object* v_00_u03b1_1183_, lean_object* v_ref_1184_, lean_object* v_msg_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_1184_, v_msg_1185_, v___y_1186_, v___y_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___boxed(lean_object* v_00_u03b1_1190_, lean_object* v_ref_1191_, lean_object* v_msg_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(v_00_u03b1_1190_, v_ref_1191_, v_msg_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v_ref_1191_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(lean_object* v_msgData_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msgData_1197_, v___y_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(v_msgData_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(lean_object* v_00_u03b1_1207_, lean_object* v_msg_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_1208_, v___y_1209_, v___y_1210_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1213_, lean_object* v_msg_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(v_00_u03b1_1213_, v_msg_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(lean_object* v_msgData_1219_, lean_object* v_macroStack_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_1219_, v_macroStack_1220_, v___y_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1225_, lean_object* v_macroStack_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(v_msgData_1225_, v_macroStack_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1(){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1259_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1260_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12));
v___x_1261_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10));
v___x_1262_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed), 4, 0);
v___x_1263_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1259_, v___x_1260_, v___x_1261_, v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___boxed(lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
return v_res_1265_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3));
v___x_1274_ = l_String_toRawSubstring_x27(v___x_1273_);
return v___x_1274_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6));
v___x_1279_ = l_String_toRawSubstring_x27(v___x_1278_);
return v___x_1279_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12));
v___x_1292_ = l_String_toRawSubstring_x27(v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15));
v___x_1297_ = l_String_toRawSubstring_x27(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21));
v___x_1305_ = l_String_toRawSubstring_x27(v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(lean_object* v_stx_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___x_1356_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; uint8_t v___x_1376_; 
v___x_1356_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1));
lean_inc(v_stx_1330_);
v___x_1376_ = l_Lean_Syntax_isOfKind(v_stx_1330_, v___x_1356_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1378_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1330_, v___x_1377_, v_a_1331_, v_a_1332_);
lean_dec(v_stx_1330_);
return v___x_1378_;
}
else
{
lean_object* v___x_1379_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; uint8_t v___y_1513_; lean_object* v___y_1514_; lean_object* v_wds_x3f_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v_wds_x3f_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v_pkg_x3f_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v_attrs_x3f_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v_doc_x3f_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1763_ = l_Lean_Syntax_getArg(v_stx_1330_, v___x_1379_);
v___x_1764_ = l_Lean_Syntax_isNone(v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1763_);
v___x_1766_ = l_Lean_Syntax_matchesNull(v___x_1763_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec(v___x_1763_);
v___x_1767_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1768_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1330_, v___x_1767_, v_a_1331_, v_a_1332_);
lean_dec(v_stx_1330_);
return v___x_1768_;
}
else
{
lean_object* v_doc_x3f_1769_; lean_object* v___x_1770_; 
v_doc_x3f_1769_ = l_Lean_Syntax_getArg(v___x_1763_, v___x_1379_);
lean_dec(v___x_1763_);
v___x_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_doc_x3f_1769_);
v_doc_x3f_1751_ = v___x_1770_;
v___y_1752_ = v_a_1331_;
v___y_1753_ = v_a_1332_;
goto v___jp_1750_;
}
}
else
{
lean_object* v___x_1771_; 
lean_dec(v___x_1763_);
v___x_1771_ = lean_box(0);
v_doc_x3f_1751_ = v___x_1771_;
v___y_1752_ = v_a_1331_;
v___y_1753_ = v_a_1332_;
goto v___jp_1750_;
}
v___jp_1380_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_inc_ref_n(v___y_1385_, 2);
v___x_1402_ = l_Array_append___redArg(v___y_1385_, v___y_1401_);
lean_dec_ref(v___y_1401_);
lean_inc_n(v___y_1393_, 8);
lean_inc_n(v___y_1390_, 41);
v___x_1403_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1403_, 0, v___y_1390_);
lean_ctor_set(v___x_1403_, 1, v___y_1393_);
lean_ctor_set(v___x_1403_, 2, v___x_1402_);
v___x_1404_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15));
lean_inc_ref_n(v___y_1398_, 9);
lean_inc_ref_n(v___y_1391_, 13);
lean_inc_ref_n(v___y_1387_, 13);
v___x_1405_ = l_Lean_Name_mkStr4(v___y_1387_, v___y_1391_, v___y_1398_, v___x_1404_);
v___x_1406_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16));
v___x_1407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___y_1390_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38));
v___x_1409_ = l_Lean_Syntax_SepArray_ofElems(v___x_1408_, v___y_1399_);
lean_dec_ref(v___y_1399_);
v___x_1410_ = l_Array_append___redArg(v___y_1385_, v___x_1409_);
lean_dec_ref(v___x_1409_);
v___x_1411_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1411_, 0, v___y_1390_);
lean_ctor_set(v___x_1411_, 1, v___y_1393_);
lean_ctor_set(v___x_1411_, 2, v___x_1410_);
v___x_1412_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17));
v___x_1413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___y_1390_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = l_Lean_Syntax_node3(v___y_1390_, v___x_1405_, v___x_1407_, v___x_1411_, v___x_1413_);
v___x_1415_ = l_Lean_Syntax_node1(v___y_1390_, v___y_1393_, v___x_1414_);
lean_inc_n(v___y_1400_, 21);
v___x_1416_ = l_Lean_Syntax_node7(v___y_1390_, v___y_1388_, v___x_1403_, v___x_1415_, v___y_1400_, v___y_1400_, v___y_1400_, v___y_1400_, v___y_1400_);
v___x_1417_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5));
lean_inc_ref_n(v___y_1392_, 3);
v___x_1418_ = l_Lean_Name_mkStr4(v___y_1387_, v___y_1391_, v___y_1392_, v___x_1417_);
v___x_1419_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6));
v___x_1420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___y_1390_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_1422_ = l_Lean_Name_mkStr4(v___y_1387_, v___y_1391_, v___y_1392_, v___x_1421_);
v___x_1423_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4);
v___x_1424_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5));
lean_inc_n(v___y_1394_, 3);
lean_inc_n(v___y_1389_, 3);
v___x_1425_ = l_Lean_addMacroScope(v___y_1389_, v___x_1424_, v___y_1394_);
lean_inc_n(v___y_1383_, 4);
v___x_1426_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1426_, 0, v___y_1390_);
lean_ctor_set(v___x_1426_, 1, v___x_1423_);
lean_ctor_set(v___x_1426_, 2, v___x_1425_);
lean_ctor_set(v___x_1426_, 3, v___y_1383_);
v___x_1427_ = l_Lean_Syntax_node2(v___y_1390_, v___x_1422_, v___x_1426_, v___y_1400_);
v___x_1428_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_1429_ = l_Lean_Name_mkStr4(v___y_1387_, v___y_1391_, v___y_1392_, v___x_1428_);
v___x_1430_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_1431_ = l_Lean_Name_mkStr4(v___y_1387_, v___y_1391_, v___y_1398_, v___x_1430_);
v___x_1432_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_1433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___y_1390_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7);
v___x_1435_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8));
v___x_1436_ = l_Lean_addMacroScope(v___y_1389_, v___x_1435_, v___y_1394_);
v___x_1437_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10));
v___x_1438_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11));
v___x_1439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
lean_ctor_set(v___x_1439_, 1, v___y_1383_);
v___x_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1437_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1441_, 0, v___y_1390_);
lean_ctor_set(v___x_1441_, 1, v___x_1434_);
lean_ctor_set(v___x_1441_, 2, v___x_1436_);
lean_ctor_set(v___x_1441_, 3, v___x_1440_);
v___x_1442_ = l_Lean_Syntax_node2(v___y_1390_, v___x_1431_, v___x_1433_, v___x_1441_);
v___x_1443_ = l_Lean_Syntax_node1(v___y_1390_, v___y_1393_, v___x_1442_);
v___x_1444_ = l_Lean_Syntax_node2(v___y_1390_, v___x_1429_, v___y_1400_, v___x_1443_);
v___x_1445_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37));
v___x_1446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___y_1390_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
v___x_1448_ = l_Lean_Name_mkStr4(v___y_1387_, v___y_1391_, v___y_1398_, v___x_1447_);
v___x_1449_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___x_1450_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___y_1390_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31));
v___x_1452_ = l_Lean_Name_mkStr4(v___y_1387_, v___y_1391_, v___y_1398_, v___x_1451_);
v___x_1453_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31));
v___x_1454_ = l_Lean_Name_mkStr4(v___y_1387_, v___y_1391_, v___y_1398_, v___x_1453_);
v___x_1455_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32));
v___x_1456_ = l_Lean_Name_mkStr4(v___y_1387_, v___y_1391_, v___y_1398_, v___x_1455_);
v___x_1457_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13);
v___x_1458_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14));
v___x_1459_ = l_Lean_addMacroScope(v___y_1389_, v___x_1458_, v___y_1394_);
v___x_1460_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1460_, 0, v___y_1390_);
lean_ctor_set(v___x_1460_, 1, v___x_1457_);
lean_ctor_set(v___x_1460_, 2, v___x_1459_);
lean_ctor_set(v___x_1460_, 3, v___y_1383_);
lean_inc(v___x_1456_);
v___x_1461_ = l_Lean_Syntax_node2(v___y_1390_, v___x_1456_, v___x_1460_, v___y_1400_);
v___x_1462_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36));
v___x_1463_ = l_Lean_Name_mkStr4(v___y_1387_, v___y_1391_, v___y_1398_, v___x_1462_);
v___x_1464_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9));
v___x_1465_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10));
v___x_1466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___y_1390_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = l_Lean_Syntax_node1(v___y_1390_, v___x_1464_, v___x_1466_);
lean_inc_ref_n(v___x_1446_, 2);
lean_inc(v___x_1463_);
v___x_1468_ = l_Lean_Syntax_node3(v___y_1390_, v___x_1463_, v___x_1446_, v___y_1400_, v___x_1467_);
v___x_1469_ = l_Lean_Syntax_node3(v___y_1390_, v___y_1393_, v___y_1400_, v___y_1400_, v___x_1468_);
lean_inc(v___x_1454_);
v___x_1470_ = l_Lean_Syntax_node2(v___y_1390_, v___x_1454_, v___x_1461_, v___x_1469_);
v___x_1471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___y_1390_);
lean_ctor_set(v___x_1471_, 1, v___x_1408_);
v___x_1472_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16);
v___x_1473_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17));
v___x_1474_ = l_Lean_addMacroScope(v___y_1389_, v___x_1473_, v___y_1394_);
v___x_1475_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1475_, 0, v___y_1390_);
lean_ctor_set(v___x_1475_, 1, v___x_1472_);
lean_ctor_set(v___x_1475_, 2, v___x_1474_);
lean_ctor_set(v___x_1475_, 3, v___y_1383_);
v___x_1476_ = l_Lean_Syntax_node2(v___y_1390_, v___x_1456_, v___x_1475_, v___y_1400_);
v___x_1477_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18));
v___x_1478_ = l_Lean_Name_mkStr4(v___y_1387_, v___y_1391_, v___y_1398_, v___x_1477_);
v___x_1479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___y_1390_);
lean_ctor_set(v___x_1479_, 1, v___x_1477_);
v___x_1480_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19));
v___x_1481_ = l_Lean_Name_mkStr4(v___y_1387_, v___y_1391_, v___y_1398_, v___x_1480_);
v___x_1482_ = l_Lean_Syntax_node1(v___y_1390_, v___y_1393_, v___y_1382_);
v___x_1483_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20));
v___x_1484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___y_1390_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = l_Lean_Syntax_node4(v___y_1390_, v___x_1481_, v___x_1482_, v___y_1400_, v___x_1484_, v___y_1397_);
v___x_1486_ = l_Lean_Syntax_node2(v___y_1390_, v___x_1478_, v___x_1479_, v___x_1485_);
v___x_1487_ = l_Lean_Syntax_node3(v___y_1390_, v___x_1463_, v___x_1446_, v___y_1400_, v___x_1486_);
v___x_1488_ = l_Lean_Syntax_node3(v___y_1390_, v___y_1393_, v___y_1400_, v___y_1400_, v___x_1487_);
v___x_1489_ = l_Lean_Syntax_node2(v___y_1390_, v___x_1454_, v___x_1476_, v___x_1488_);
v___x_1490_ = l_Lean_Syntax_node3(v___y_1390_, v___y_1393_, v___x_1470_, v___x_1471_, v___x_1489_);
v___x_1491_ = l_Lean_Syntax_node1(v___y_1390_, v___x_1452_, v___x_1490_);
v___x_1492_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45));
v___x_1493_ = l_Lean_Name_mkStr4(v___y_1387_, v___y_1391_, v___y_1398_, v___x_1492_);
v___x_1494_ = l_Lean_Syntax_node1(v___y_1390_, v___x_1493_, v___y_1400_);
v___x_1495_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46));
v___x_1496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1390_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = l_Lean_Syntax_node6(v___y_1390_, v___x_1448_, v___x_1450_, v___y_1400_, v___x_1491_, v___x_1494_, v___y_1400_, v___x_1496_);
lean_inc(v___y_1381_);
v___x_1498_ = l_Lean_Syntax_node2(v___y_1390_, v___y_1381_, v___y_1400_, v___y_1400_);
if (lean_obj_tag(v___y_1396_) == 1)
{
lean_object* v_val_1499_; lean_object* v___x_1500_; 
v_val_1499_ = lean_ctor_get(v___y_1396_, 0);
lean_inc(v_val_1499_);
lean_dec_ref(v___y_1396_);
v___x_1500_ = l_Array_mkArray1___redArg(v_val_1499_);
v___y_1334_ = v___x_1497_;
v___y_1335_ = v___x_1418_;
v___y_1336_ = v___x_1427_;
v___y_1337_ = v___y_1384_;
v___y_1338_ = v___y_1385_;
v___y_1339_ = v___y_1386_;
v___y_1340_ = v___y_1390_;
v___y_1341_ = v___y_1393_;
v___y_1342_ = v___x_1420_;
v___y_1343_ = v___x_1498_;
v___y_1344_ = v___x_1444_;
v___y_1345_ = v___y_1395_;
v___y_1346_ = v___x_1416_;
v___y_1347_ = v___x_1446_;
v___y_1348_ = v___y_1400_;
v___y_1349_ = v___x_1500_;
goto v___jp_1333_;
}
else
{
lean_object* v___x_1501_; 
lean_dec(v___y_1396_);
v___x_1501_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___y_1334_ = v___x_1497_;
v___y_1335_ = v___x_1418_;
v___y_1336_ = v___x_1427_;
v___y_1337_ = v___y_1384_;
v___y_1338_ = v___y_1385_;
v___y_1339_ = v___y_1386_;
v___y_1340_ = v___y_1390_;
v___y_1341_ = v___y_1393_;
v___y_1342_ = v___x_1420_;
v___y_1343_ = v___x_1498_;
v___y_1344_ = v___x_1444_;
v___y_1345_ = v___y_1395_;
v___y_1346_ = v___x_1416_;
v___y_1347_ = v___x_1446_;
v___y_1348_ = v___y_1400_;
v___y_1349_ = v___x_1501_;
goto v___jp_1333_;
}
}
v___jp_1502_:
{
lean_object* v_methods_1518_; lean_object* v_quotContext_1519_; lean_object* v_currMacroScope_1520_; lean_object* v_currRecDepth_1521_; lean_object* v_maxRecDepth_1522_; lean_object* v_ref_1523_; lean_object* v_ref_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_methods_1518_ = lean_ctor_get(v___y_1516_, 0);
v_quotContext_1519_ = lean_ctor_get(v___y_1516_, 1);
v_currMacroScope_1520_ = lean_ctor_get(v___y_1516_, 2);
v_currRecDepth_1521_ = lean_ctor_get(v___y_1516_, 3);
v_maxRecDepth_1522_ = lean_ctor_get(v___y_1516_, 4);
v_ref_1523_ = lean_ctor_get(v___y_1516_, 5);
v_ref_1524_ = l_Lean_replaceRef(v___y_1511_, v_ref_1523_);
lean_dec(v___y_1511_);
lean_inc(v_ref_1524_);
lean_inc(v_maxRecDepth_1522_);
lean_inc(v_currRecDepth_1521_);
lean_inc(v_currMacroScope_1520_);
lean_inc(v_quotContext_1519_);
lean_inc(v_methods_1518_);
v___x_1525_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1525_, 0, v_methods_1518_);
lean_ctor_set(v___x_1525_, 1, v_quotContext_1519_);
lean_ctor_set(v___x_1525_, 2, v_currMacroScope_1520_);
lean_ctor_set(v___x_1525_, 3, v_currRecDepth_1521_);
lean_ctor_set(v___x_1525_, 4, v_maxRecDepth_1522_);
lean_ctor_set(v___x_1525_, 5, v_ref_1524_);
v___x_1526_ = l_Lake_DSL_expandOptSimpleBinder(v___y_1504_, v___x_1525_, v___y_1517_);
lean_dec_ref(v___x_1525_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v_a_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
v_a_1528_ = lean_ctor_get(v___x_1526_, 1);
lean_inc(v_a_1528_);
lean_dec_ref(v___x_1526_);
v___x_1529_ = l_Lean_SourceInfo_fromRef(v_ref_1524_, v___y_1513_);
lean_dec(v_ref_1524_);
v___x_1530_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_1531_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47));
lean_inc_ref_n(v___y_1512_, 5);
lean_inc_ref_n(v___y_1510_, 5);
v___x_1532_ = l_Lean_Name_mkStr4(v___y_1510_, v___y_1512_, v___x_1530_, v___x_1531_);
v___x_1533_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48));
v___x_1534_ = l_Lean_Name_mkStr4(v___y_1510_, v___y_1512_, v___x_1530_, v___x_1533_);
v___x_1535_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_1536_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___x_1529_, 5);
v___x_1537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1529_);
lean_ctor_set(v___x_1537_, 1, v___x_1535_);
lean_ctor_set(v___x_1537_, 2, v___x_1536_);
lean_inc_ref_n(v___x_1537_, 2);
v___x_1538_ = l_Lean_Syntax_node1(v___x_1529_, v___x_1534_, v___x_1537_);
v___x_1539_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53));
v___x_1540_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54));
v___x_1541_ = l_Lean_Name_mkStr4(v___y_1510_, v___y_1512_, v___x_1539_, v___x_1540_);
v___x_1542_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22);
v___x_1543_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24));
lean_inc(v_currMacroScope_1520_);
lean_inc(v_quotContext_1519_);
v___x_1544_ = l_Lean_addMacroScope(v_quotContext_1519_, v___x_1543_, v_currMacroScope_1520_);
v___x_1545_ = lean_box(0);
v___x_1546_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1529_);
lean_ctor_set(v___x_1546_, 1, v___x_1542_);
lean_ctor_set(v___x_1546_, 2, v___x_1544_);
lean_ctor_set(v___x_1546_, 3, v___x_1545_);
v___x_1547_ = l_Lean_Syntax_node2(v___x_1529_, v___x_1541_, v___x_1546_, v___x_1537_);
v___x_1548_ = l_Lean_Syntax_node2(v___x_1529_, v___x_1532_, v___x_1538_, v___x_1547_);
v___x_1549_ = lean_mk_empty_array_with_capacity(v___y_1506_);
v___x_1550_ = lean_array_push(v___x_1549_, v___x_1548_);
v___x_1551_ = l_Lake_DSL_expandAttrs(v___y_1509_);
v___x_1552_ = l_Array_append___redArg(v___x_1550_, v___x_1551_);
lean_dec_ref(v___x_1551_);
v___x_1553_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_1514_, 2);
v___x_1554_ = l_Lean_Name_mkStr4(v___y_1510_, v___y_1512_, v___y_1514_, v___x_1553_);
v___x_1555_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_1556_ = l_Lean_Name_mkStr4(v___y_1510_, v___y_1512_, v___y_1514_, v___x_1555_);
if (lean_obj_tag(v___y_1507_) == 1)
{
lean_object* v_val_1557_; lean_object* v___x_1558_; 
v_val_1557_ = lean_ctor_get(v___y_1507_, 0);
lean_inc(v_val_1557_);
lean_dec_ref(v___y_1507_);
v___x_1558_ = l_Array_mkArray1___redArg(v_val_1557_);
lean_inc(v_currMacroScope_1520_);
lean_inc(v_quotContext_1519_);
v___y_1381_ = v___y_1503_;
v___y_1382_ = v_a_1527_;
v___y_1383_ = v___x_1545_;
v___y_1384_ = v_a_1528_;
v___y_1385_ = v___x_1536_;
v___y_1386_ = v___y_1508_;
v___y_1387_ = v___y_1510_;
v___y_1388_ = v___x_1556_;
v___y_1389_ = v_quotContext_1519_;
v___y_1390_ = v___x_1529_;
v___y_1391_ = v___y_1512_;
v___y_1392_ = v___y_1514_;
v___y_1393_ = v___x_1535_;
v___y_1394_ = v_currMacroScope_1520_;
v___y_1395_ = v___x_1554_;
v___y_1396_ = v_wds_x3f_1515_;
v___y_1397_ = v___y_1505_;
v___y_1398_ = v___x_1530_;
v___y_1399_ = v___x_1552_;
v___y_1400_ = v___x_1537_;
v___y_1401_ = v___x_1558_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1559_; 
lean_dec(v___y_1507_);
v___x_1559_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
lean_inc(v_currMacroScope_1520_);
lean_inc(v_quotContext_1519_);
v___y_1381_ = v___y_1503_;
v___y_1382_ = v_a_1527_;
v___y_1383_ = v___x_1545_;
v___y_1384_ = v_a_1528_;
v___y_1385_ = v___x_1536_;
v___y_1386_ = v___y_1508_;
v___y_1387_ = v___y_1510_;
v___y_1388_ = v___x_1556_;
v___y_1389_ = v_quotContext_1519_;
v___y_1390_ = v___x_1529_;
v___y_1391_ = v___y_1512_;
v___y_1392_ = v___y_1514_;
v___y_1393_ = v___x_1535_;
v___y_1394_ = v_currMacroScope_1520_;
v___y_1395_ = v___x_1554_;
v___y_1396_ = v_wds_x3f_1515_;
v___y_1397_ = v___y_1505_;
v___y_1398_ = v___x_1530_;
v___y_1399_ = v___x_1552_;
v___y_1400_ = v___x_1537_;
v___y_1401_ = v___x_1559_;
goto v___jp_1380_;
}
}
else
{
lean_object* v_a_1560_; lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec(v_ref_1524_);
lean_dec(v_wds_x3f_1515_);
lean_dec(v___y_1509_);
lean_dec(v___y_1507_);
lean_dec(v___y_1505_);
v_a_1560_ = lean_ctor_get(v___x_1526_, 0);
v_a_1561_ = lean_ctor_get(v___x_1526_, 1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1526_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_inc(v_a_1560_);
lean_dec(v___x_1526_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1560_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
v___jp_1569_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_inc_ref_n(v___y_1571_, 2);
v___x_1584_ = l_Array_append___redArg(v___y_1571_, v___y_1583_);
lean_dec_ref(v___y_1583_);
lean_inc_n(v___y_1573_, 2);
lean_inc_n(v___y_1576_, 6);
v___x_1585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1585_, 0, v___y_1576_);
lean_ctor_set(v___x_1585_, 1, v___y_1573_);
lean_ctor_set(v___x_1585_, 2, v___x_1584_);
v___x_1586_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_1587_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25));
lean_inc_ref_n(v___y_1577_, 2);
lean_inc_ref_n(v___y_1570_, 2);
v___x_1588_ = l_Lean_Name_mkStr4(v___y_1570_, v___y_1577_, v___x_1586_, v___x_1587_);
v___x_1589_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37));
v___x_1590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___y_1576_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
lean_inc_ref(v___y_1578_);
v___x_1591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___y_1576_);
lean_ctor_set(v___x_1591_, 1, v___y_1578_);
lean_inc(v___y_1579_);
v___x_1592_ = l_Lean_Syntax_node2(v___y_1576_, v___y_1579_, v___x_1591_, v___y_1582_);
v___x_1593_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26));
v___x_1594_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27));
v___x_1595_ = l_Lean_Name_mkStr4(v___y_1570_, v___y_1577_, v___x_1593_, v___x_1594_);
v___x_1596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1596_, 0, v___y_1576_);
lean_ctor_set(v___x_1596_, 1, v___y_1573_);
lean_ctor_set(v___x_1596_, 2, v___y_1571_);
lean_inc_ref(v___x_1596_);
v___x_1597_ = l_Lean_Syntax_node2(v___y_1576_, v___x_1595_, v___x_1596_, v___x_1596_);
if (lean_obj_tag(v___y_1574_) == 1)
{
lean_object* v_val_1598_; lean_object* v___x_1599_; 
v_val_1598_ = lean_ctor_get(v___y_1574_, 0);
lean_inc(v_val_1598_);
lean_dec_ref(v___y_1574_);
v___x_1599_ = l_Array_mkArray1___redArg(v_val_1598_);
v___y_1358_ = v___x_1585_;
v___y_1359_ = v___x_1588_;
v___y_1360_ = v___y_1571_;
v___y_1361_ = v___x_1597_;
v___y_1362_ = v___y_1572_;
v___y_1363_ = v___x_1590_;
v___y_1364_ = v___y_1573_;
v___y_1365_ = v___y_1580_;
v___y_1366_ = v___y_1581_;
v___y_1367_ = v___y_1575_;
v___y_1368_ = v___x_1592_;
v___y_1369_ = v___y_1576_;
v___y_1370_ = v___x_1599_;
goto v___jp_1357_;
}
else
{
lean_object* v___x_1600_; 
lean_dec(v___y_1574_);
v___x_1600_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___y_1358_ = v___x_1585_;
v___y_1359_ = v___x_1588_;
v___y_1360_ = v___y_1571_;
v___y_1361_ = v___x_1597_;
v___y_1362_ = v___y_1572_;
v___y_1363_ = v___x_1590_;
v___y_1364_ = v___y_1573_;
v___y_1365_ = v___y_1580_;
v___y_1366_ = v___y_1581_;
v___y_1367_ = v___y_1575_;
v___y_1368_ = v___x_1592_;
v___y_1369_ = v___y_1576_;
v___y_1370_ = v___x_1600_;
goto v___jp_1357_;
}
}
v___jp_1601_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_inc_ref(v___y_1603_);
v___x_1616_ = l_Array_append___redArg(v___y_1603_, v___y_1615_);
lean_dec_ref(v___y_1615_);
lean_inc(v___y_1606_);
lean_inc(v___y_1609_);
v___x_1617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1617_, 0, v___y_1609_);
lean_ctor_set(v___x_1617_, 1, v___y_1606_);
lean_ctor_set(v___x_1617_, 2, v___x_1616_);
v___x_1618_ = l_Lean_SourceInfo_fromRef(v___y_1613_, v___x_1376_);
lean_dec(v___y_1613_);
v___x_1619_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23));
v___x_1620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
if (lean_obj_tag(v___y_1604_) == 1)
{
lean_object* v_val_1621_; lean_object* v___x_1622_; 
v_val_1621_ = lean_ctor_get(v___y_1604_, 0);
lean_inc(v_val_1621_);
lean_dec_ref(v___y_1604_);
v___x_1622_ = l_Array_mkArray1___redArg(v_val_1621_);
v___y_1570_ = v___y_1602_;
v___y_1571_ = v___y_1603_;
v___y_1572_ = v___y_1605_;
v___y_1573_ = v___y_1606_;
v___y_1574_ = v___y_1607_;
v___y_1575_ = v___y_1608_;
v___y_1576_ = v___y_1609_;
v___y_1577_ = v___y_1610_;
v___y_1578_ = v___y_1611_;
v___y_1579_ = v___y_1612_;
v___y_1580_ = v___x_1620_;
v___y_1581_ = v___x_1617_;
v___y_1582_ = v___y_1614_;
v___y_1583_ = v___x_1622_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1623_; 
lean_dec(v___y_1604_);
v___x_1623_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___y_1570_ = v___y_1602_;
v___y_1571_ = v___y_1603_;
v___y_1572_ = v___y_1605_;
v___y_1573_ = v___y_1606_;
v___y_1574_ = v___y_1607_;
v___y_1575_ = v___y_1608_;
v___y_1576_ = v___y_1609_;
v___y_1577_ = v___y_1610_;
v___y_1578_ = v___y_1611_;
v___y_1579_ = v___y_1612_;
v___y_1580_ = v___x_1620_;
v___y_1581_ = v___x_1617_;
v___y_1582_ = v___y_1614_;
v___y_1583_ = v___x_1623_;
goto v___jp_1569_;
}
}
v___jp_1624_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_inc_ref(v___y_1626_);
v___x_1639_ = l_Array_append___redArg(v___y_1626_, v___y_1638_);
lean_dec_ref(v___y_1638_);
lean_inc(v___y_1629_);
lean_inc(v___y_1631_);
v___x_1640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1640_, 0, v___y_1631_);
lean_ctor_set(v___x_1640_, 1, v___y_1629_);
lean_ctor_set(v___x_1640_, 2, v___x_1639_);
if (lean_obj_tag(v___y_1635_) == 1)
{
lean_object* v_val_1641_; lean_object* v___x_1642_; 
v_val_1641_ = lean_ctor_get(v___y_1635_, 0);
lean_inc(v_val_1641_);
lean_dec_ref(v___y_1635_);
v___x_1642_ = l_Array_mkArray1___redArg(v_val_1641_);
v___y_1602_ = v___y_1625_;
v___y_1603_ = v___y_1626_;
v___y_1604_ = v___y_1627_;
v___y_1605_ = v___y_1628_;
v___y_1606_ = v___y_1629_;
v___y_1607_ = v___y_1630_;
v___y_1608_ = v___x_1640_;
v___y_1609_ = v___y_1631_;
v___y_1610_ = v___y_1632_;
v___y_1611_ = v___y_1633_;
v___y_1612_ = v___y_1634_;
v___y_1613_ = v___y_1636_;
v___y_1614_ = v___y_1637_;
v___y_1615_ = v___x_1642_;
goto v___jp_1601_;
}
else
{
lean_object* v___x_1643_; 
lean_dec(v___y_1635_);
v___x_1643_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___y_1602_ = v___y_1625_;
v___y_1603_ = v___y_1626_;
v___y_1604_ = v___y_1627_;
v___y_1605_ = v___y_1628_;
v___y_1606_ = v___y_1629_;
v___y_1607_ = v___y_1630_;
v___y_1608_ = v___x_1640_;
v___y_1609_ = v___y_1631_;
v___y_1610_ = v___y_1632_;
v___y_1611_ = v___y_1633_;
v___y_1612_ = v___y_1634_;
v___y_1613_ = v___y_1636_;
v___y_1614_ = v___y_1637_;
v___y_1615_ = v___x_1643_;
goto v___jp_1601_;
}
}
v___jp_1644_:
{
lean_object* v_ref_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_ref_1657_ = lean_ctor_get(v___y_1655_, 5);
v___x_1658_ = 0;
v___x_1659_ = l_Lean_SourceInfo_fromRef(v_ref_1657_, v___x_1658_);
v___x_1660_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_1661_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
if (lean_obj_tag(v___y_1647_) == 1)
{
lean_object* v_val_1662_; lean_object* v___x_1663_; 
v_val_1662_ = lean_ctor_get(v___y_1647_, 0);
lean_inc(v_val_1662_);
lean_dec_ref(v___y_1647_);
v___x_1663_ = l_Array_mkArray1___redArg(v_val_1662_);
v___y_1625_ = v___y_1645_;
v___y_1626_ = v___x_1661_;
v___y_1627_ = v___y_1646_;
v___y_1628_ = v___y_1656_;
v___y_1629_ = v___x_1660_;
v___y_1630_ = v_wds_x3f_1654_;
v___y_1631_ = v___x_1659_;
v___y_1632_ = v___y_1653_;
v___y_1633_ = v___y_1648_;
v___y_1634_ = v___y_1650_;
v___y_1635_ = v___y_1649_;
v___y_1636_ = v___y_1651_;
v___y_1637_ = v___y_1652_;
v___y_1638_ = v___x_1663_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1664_; 
lean_dec(v___y_1647_);
v___x_1664_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___y_1625_ = v___y_1645_;
v___y_1626_ = v___x_1661_;
v___y_1627_ = v___y_1646_;
v___y_1628_ = v___y_1656_;
v___y_1629_ = v___x_1660_;
v___y_1630_ = v_wds_x3f_1654_;
v___y_1631_ = v___x_1659_;
v___y_1632_ = v___y_1653_;
v___y_1633_ = v___y_1648_;
v___y_1634_ = v___y_1650_;
v___y_1635_ = v___y_1649_;
v___y_1636_ = v___y_1651_;
v___y_1637_ = v___y_1652_;
v___y_1638_ = v___x_1664_;
goto v___jp_1624_;
}
}
v___jp_1665_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1675_ = lean_unsigned_to_nat(4u);
v___x_1676_ = l_Lean_Syntax_getArg(v_stx_1330_, v___x_1675_);
v___x_1677_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26));
lean_inc(v___x_1676_);
v___x_1678_ = l_Lean_Syntax_isOfKind(v___x_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1679_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1680_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_1681_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_1682_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27));
lean_inc(v___x_1676_);
v___x_1683_ = l_Lean_Syntax_isOfKind(v___x_1676_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec(v___x_1676_);
lean_dec(v_pkg_x3f_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v___y_1669_);
v___x_1684_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1685_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1330_, v___x_1684_, v___y_1673_, v___y_1674_);
lean_dec(v_stx_1330_);
return v___x_1685_;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1686_ = l_Lean_Syntax_getArg(v___x_1676_, v___y_1666_);
v___x_1687_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28));
lean_inc(v___x_1686_);
v___x_1688_ = l_Lean_Syntax_isOfKind(v___x_1686_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec(v___x_1686_);
lean_dec(v___x_1676_);
lean_dec(v_pkg_x3f_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v___y_1669_);
v___x_1689_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1690_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1330_, v___x_1689_, v___y_1673_, v___y_1674_);
lean_dec(v_stx_1330_);
return v___x_1690_;
}
else
{
lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1691_ = l_Lean_Syntax_getArg(v___x_1686_, v___x_1379_);
v___x_1692_ = l_Lean_Syntax_matchesNull(v___x_1691_, v___x_1379_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_dec(v___x_1686_);
lean_dec(v___x_1676_);
lean_dec(v_pkg_x3f_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v___y_1669_);
v___x_1693_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1694_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1330_, v___x_1693_, v___y_1673_, v___y_1674_);
lean_dec(v_stx_1330_);
return v___x_1694_;
}
else
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = l_Lean_Syntax_getArg(v___x_1686_, v___y_1668_);
lean_dec(v___x_1686_);
v___x_1696_ = l_Lean_Syntax_matchesNull(v___x_1695_, v___x_1379_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_dec(v___x_1676_);
lean_dec(v_pkg_x3f_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v___y_1669_);
v___x_1697_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1698_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1330_, v___x_1697_, v___y_1673_, v___y_1674_);
lean_dec(v_stx_1330_);
return v___x_1698_;
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1699_ = l_Lean_Syntax_getArg(v___x_1676_, v___y_1668_);
v___x_1700_ = l_Lean_Syntax_getArg(v___x_1676_, v___y_1667_);
lean_dec(v___x_1676_);
v___x_1701_ = l_Lean_Syntax_isNone(v___x_1700_);
if (v___x_1701_ == 0)
{
uint8_t v___x_1702_; 
lean_inc(v___x_1700_);
v___x_1702_ = l_Lean_Syntax_matchesNull(v___x_1700_, v___y_1668_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec(v___x_1700_);
lean_dec(v___x_1699_);
lean_dec(v_pkg_x3f_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v___y_1669_);
v___x_1703_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1704_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1330_, v___x_1703_, v___y_1673_, v___y_1674_);
lean_dec(v_stx_1330_);
return v___x_1704_;
}
else
{
lean_object* v_wds_x3f_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v_wds_x3f_1705_ = l_Lean_Syntax_getArg(v___x_1700_, v___x_1379_);
lean_dec(v___x_1700_);
v___x_1706_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_1705_);
v___x_1707_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1705_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec(v_wds_x3f_1705_);
lean_dec(v___x_1699_);
lean_dec(v_pkg_x3f_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v___y_1669_);
v___x_1708_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1709_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1330_, v___x_1708_, v___y_1673_, v___y_1674_);
lean_dec(v_stx_1330_);
return v___x_1709_;
}
else
{
lean_object* v___x_1710_; 
lean_dec(v_stx_1330_);
v___x_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_wds_x3f_1705_);
v___y_1503_ = v___x_1687_;
v___y_1504_ = v_pkg_x3f_1672_;
v___y_1505_ = v___x_1699_;
v___y_1506_ = v___y_1668_;
v___y_1507_ = v___y_1669_;
v___y_1508_ = v___x_1682_;
v___y_1509_ = v___y_1670_;
v___y_1510_ = v___x_1679_;
v___y_1511_ = v___y_1671_;
v___y_1512_ = v___x_1680_;
v___y_1513_ = v___x_1678_;
v___y_1514_ = v___x_1681_;
v_wds_x3f_1515_ = v___x_1710_;
v___y_1516_ = v___y_1673_;
v___y_1517_ = v___y_1674_;
goto v___jp_1502_;
}
}
}
else
{
lean_object* v___x_1711_; 
lean_dec(v___x_1700_);
lean_dec(v_stx_1330_);
v___x_1711_ = lean_box(0);
v___y_1503_ = v___x_1687_;
v___y_1504_ = v_pkg_x3f_1672_;
v___y_1505_ = v___x_1699_;
v___y_1506_ = v___y_1668_;
v___y_1507_ = v___y_1669_;
v___y_1508_ = v___x_1682_;
v___y_1509_ = v___y_1670_;
v___y_1510_ = v___x_1679_;
v___y_1511_ = v___y_1671_;
v___y_1512_ = v___x_1680_;
v___y_1513_ = v___x_1678_;
v___y_1514_ = v___x_1681_;
v_wds_x3f_1515_ = v___x_1711_;
v___y_1516_ = v___y_1673_;
v___y_1517_ = v___y_1674_;
goto v___jp_1502_;
}
}
}
}
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1712_ = l_Lean_Syntax_getArg(v___x_1676_, v___x_1379_);
v___x_1713_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1714_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_1715_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29));
v___x_1716_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30));
lean_inc(v___x_1712_);
v___x_1717_ = l_Lean_Syntax_isOfKind(v___x_1712_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec(v___x_1712_);
lean_dec(v___x_1676_);
lean_dec(v_pkg_x3f_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v___y_1669_);
v___x_1718_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1719_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1330_, v___x_1718_, v___y_1673_, v___y_1674_);
lean_dec(v_stx_1330_);
return v___x_1719_;
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1720_ = l_Lean_Syntax_getArg(v___x_1712_, v___y_1668_);
lean_dec(v___x_1712_);
v___x_1721_ = l_Lean_Syntax_getArg(v___x_1676_, v___y_1668_);
lean_dec(v___x_1676_);
v___x_1722_ = l_Lean_Syntax_isNone(v___x_1721_);
if (v___x_1722_ == 0)
{
uint8_t v___x_1723_; 
lean_inc(v___x_1721_);
v___x_1723_ = l_Lean_Syntax_matchesNull(v___x_1721_, v___y_1668_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_dec(v___x_1721_);
lean_dec(v___x_1720_);
lean_dec(v_pkg_x3f_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v___y_1669_);
v___x_1724_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1725_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1330_, v___x_1724_, v___y_1673_, v___y_1674_);
lean_dec(v_stx_1330_);
return v___x_1725_;
}
else
{
lean_object* v_wds_x3f_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_wds_x3f_1726_ = l_Lean_Syntax_getArg(v___x_1721_, v___x_1379_);
lean_dec(v___x_1721_);
v___x_1727_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_1726_);
v___x_1728_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1726_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v_wds_x3f_1726_);
lean_dec(v___x_1720_);
lean_dec(v_pkg_x3f_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v___y_1669_);
v___x_1729_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1730_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1330_, v___x_1729_, v___y_1673_, v___y_1674_);
lean_dec(v_stx_1330_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; 
lean_dec(v_stx_1330_);
v___x_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_wds_x3f_1726_);
v___y_1645_ = v___x_1713_;
v___y_1646_ = v_pkg_x3f_1672_;
v___y_1647_ = v___y_1669_;
v___y_1648_ = v___x_1715_;
v___y_1649_ = v___y_1670_;
v___y_1650_ = v___x_1716_;
v___y_1651_ = v___y_1671_;
v___y_1652_ = v___x_1720_;
v___y_1653_ = v___x_1714_;
v_wds_x3f_1654_ = v___x_1731_;
v___y_1655_ = v___y_1673_;
v___y_1656_ = v___y_1674_;
goto v___jp_1644_;
}
}
}
else
{
lean_object* v___x_1732_; 
lean_dec(v___x_1721_);
lean_dec(v_stx_1330_);
v___x_1732_ = lean_box(0);
v___y_1645_ = v___x_1713_;
v___y_1646_ = v_pkg_x3f_1672_;
v___y_1647_ = v___y_1669_;
v___y_1648_ = v___x_1715_;
v___y_1649_ = v___y_1670_;
v___y_1650_ = v___x_1716_;
v___y_1651_ = v___y_1671_;
v___y_1652_ = v___x_1720_;
v___y_1653_ = v___x_1714_;
v_wds_x3f_1654_ = v___x_1732_;
v___y_1655_ = v___y_1673_;
v___y_1656_ = v___y_1674_;
goto v___jp_1644_;
}
}
}
}
v___jp_1733_:
{
lean_object* v___x_1739_; lean_object* v_kw_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1739_ = lean_unsigned_to_nat(2u);
v_kw_1740_ = l_Lean_Syntax_getArg(v_stx_1330_, v___x_1739_);
v___x_1741_ = lean_unsigned_to_nat(3u);
v___x_1742_ = l_Lean_Syntax_getArg(v_stx_1330_, v___x_1741_);
v___x_1743_ = l_Lean_Syntax_isNone(v___x_1742_);
if (v___x_1743_ == 0)
{
uint8_t v___x_1744_; 
lean_inc(v___x_1742_);
v___x_1744_ = l_Lean_Syntax_matchesNull(v___x_1742_, v___y_1734_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_dec(v___x_1742_);
lean_dec(v_kw_1740_);
lean_dec(v_attrs_x3f_1736_);
lean_dec(v___y_1735_);
v___x_1745_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1746_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1330_, v___x_1745_, v___y_1737_, v___y_1738_);
lean_dec(v_stx_1330_);
return v___x_1746_;
}
else
{
lean_object* v_pkg_x3f_1747_; lean_object* v___x_1748_; 
v_pkg_x3f_1747_ = l_Lean_Syntax_getArg(v___x_1742_, v___x_1379_);
lean_dec(v___x_1742_);
v___x_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1748_, 0, v_pkg_x3f_1747_);
v___y_1666_ = v___x_1739_;
v___y_1667_ = v___x_1741_;
v___y_1668_ = v___y_1734_;
v___y_1669_ = v___y_1735_;
v___y_1670_ = v_attrs_x3f_1736_;
v___y_1671_ = v_kw_1740_;
v_pkg_x3f_1672_ = v___x_1748_;
v___y_1673_ = v___y_1737_;
v___y_1674_ = v___y_1738_;
goto v___jp_1665_;
}
}
else
{
lean_object* v___x_1749_; 
lean_dec(v___x_1742_);
v___x_1749_ = lean_box(0);
v___y_1666_ = v___x_1739_;
v___y_1667_ = v___x_1741_;
v___y_1668_ = v___y_1734_;
v___y_1669_ = v___y_1735_;
v___y_1670_ = v_attrs_x3f_1736_;
v___y_1671_ = v_kw_1740_;
v_pkg_x3f_1672_ = v___x_1749_;
v___y_1673_ = v___y_1737_;
v___y_1674_ = v___y_1738_;
goto v___jp_1665_;
}
}
v___jp_1750_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = l_Lean_Syntax_getArg(v_stx_1330_, v___x_1754_);
v___x_1756_ = l_Lean_Syntax_isNone(v___x_1755_);
if (v___x_1756_ == 0)
{
uint8_t v___x_1757_; 
lean_inc(v___x_1755_);
v___x_1757_ = l_Lean_Syntax_matchesNull(v___x_1755_, v___x_1754_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_dec(v___x_1755_);
lean_dec(v_doc_x3f_1751_);
v___x_1758_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1759_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1330_, v___x_1758_, v___y_1752_, v___y_1753_);
lean_dec(v_stx_1330_);
return v___x_1759_;
}
else
{
lean_object* v_attrs_x3f_1760_; lean_object* v___x_1761_; 
v_attrs_x3f_1760_ = l_Lean_Syntax_getArg(v___x_1755_, v___x_1379_);
lean_dec(v___x_1755_);
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_attrs_x3f_1760_);
v___y_1734_ = v___x_1754_;
v___y_1735_ = v_doc_x3f_1751_;
v_attrs_x3f_1736_ = v___x_1761_;
v___y_1737_ = v___y_1752_;
v___y_1738_ = v___y_1753_;
goto v___jp_1733_;
}
}
else
{
lean_object* v___x_1762_; 
lean_dec(v___x_1755_);
v___x_1762_ = lean_box(0);
v___y_1734_ = v___x_1754_;
v___y_1735_ = v_doc_x3f_1751_;
v_attrs_x3f_1736_ = v___x_1762_;
v___y_1737_ = v___y_1752_;
v___y_1738_ = v___y_1753_;
goto v___jp_1733_;
}
}
}
v___jp_1333_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_inc_ref(v___y_1338_);
v___x_1350_ = l_Array_append___redArg(v___y_1338_, v___y_1349_);
lean_dec_ref(v___y_1349_);
lean_inc(v___y_1341_);
lean_inc_n(v___y_1340_, 3);
v___x_1351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1351_, 0, v___y_1340_);
lean_ctor_set(v___x_1351_, 1, v___y_1341_);
lean_ctor_set(v___x_1351_, 2, v___x_1350_);
lean_inc(v___y_1339_);
v___x_1352_ = l_Lean_Syntax_node4(v___y_1340_, v___y_1339_, v___y_1347_, v___y_1334_, v___y_1343_, v___x_1351_);
v___x_1353_ = l_Lean_Syntax_node5(v___y_1340_, v___y_1335_, v___y_1342_, v___y_1336_, v___y_1344_, v___x_1352_, v___y_1348_);
v___x_1354_ = l_Lean_Syntax_node2(v___y_1340_, v___y_1345_, v___y_1346_, v___x_1353_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v___y_1337_);
return v___x_1355_;
}
v___jp_1357_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_inc_ref(v___y_1360_);
v___x_1371_ = l_Array_append___redArg(v___y_1360_, v___y_1370_);
lean_dec_ref(v___y_1370_);
lean_inc(v___y_1364_);
lean_inc_n(v___y_1369_, 2);
v___x_1372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1372_, 0, v___y_1369_);
lean_ctor_set(v___x_1372_, 1, v___y_1364_);
lean_ctor_set(v___x_1372_, 2, v___x_1371_);
v___x_1373_ = l_Lean_Syntax_node4(v___y_1369_, v___y_1359_, v___y_1363_, v___y_1368_, v___y_1361_, v___x_1372_);
v___x_1374_ = l_Lean_Syntax_node5(v___y_1369_, v___x_1356_, v___y_1367_, v___y_1366_, v___y_1365_, v___y_1358_, v___x_1373_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___y_1362_);
return v___x_1375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed(lean_object* v_stx_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(v_stx_1772_, v_a_1773_, v_a_1774_);
lean_dec_ref(v_a_1773_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1(){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1781_ = l_Lean_Elab_macroAttribute;
v___x_1782_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1));
v___x_1783_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1));
v___x_1784_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed), 3, 0);
v___x_1785_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1781_, v___x_1782_, v___x_1783_, v___x_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___boxed(lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
return v_res_1787_;
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
