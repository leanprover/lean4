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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lake_PackageConfig_instConfigInfo;
lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_DSL_expandAttrs(lean_object*);
extern lean_object* l_Lake_DSL_packageDeclName;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkCApp(lean_object*, lean_object*);
lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lake_Name_quoteFrom(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lake_nameExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value;
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3_value;
static lean_once_cell_t l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7_value;
static const lean_array_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "where"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "whereStructInst"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value;
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_1),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_2),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(164, 171, 248, 18, 201, 160, 43, 108)}};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value;
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_1),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(175, 253, 70, 178, 90, 186, 195, 40)}};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed configuration syntax"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23_value;
static lean_once_cell_t l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "declValWhere"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value;
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_1),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(151, 133, 86, 223, 245, 102, 246, 81)}};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValStruct"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value;
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_1),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(133, 214, 189, 204, 150, 4, 239, 13)}};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structVal"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value;
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_1),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(111, 76, 221, 200, 37, 245, 130, 150)}};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value;
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_1),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_2),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value;
static const lean_string_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "whereDecls"};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value;
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_1),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_2),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(51, 156, 180, 247, 37, 30, 126, 62)}};
static const lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34 = (const lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(97, 173, 245, 76, 54, 29, 98, 170)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "__name__"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "packageCommand"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value),LEAN_SCALAR_PTR_LITERAL(125, 54, 253, 85, 92, 174, 10, 50)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed package declaration"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "abbrev"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "PackageDecl"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_value),LEAN_SCALAR_PTR_LITERAL(225, 4, 178, 81, 27, 213, 197, 136)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value_aux_0),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_value),LEAN_SCALAR_PTR_LITERAL(253, 117, 189, 141, 218, 132, 90, 198)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29_value;
static const lean_array_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "baseName"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_value),LEAN_SCALAR_PTR_LITERAL(110, 15, 203, 48, 91, 80, 65, 181)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "origName"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_value),LEAN_SCALAR_PTR_LITERAL(60, 90, 152, 77, 27, 27, 68, 80)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "keyName"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_value),LEAN_SCALAR_PTR_LITERAL(25, 96, 4, 27, 96, 164, 24, 20)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_value),LEAN_SCALAR_PTR_LITERAL(207, 146, 87, 28, 198, 178, 209, 199)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 9, .m_data = "«package»"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "package"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value_aux_0),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value),LEAN_SCALAR_PTR_LITERAL(35, 98, 18, 79, 25, 208, 83, 100)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PackageConfig"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64_value_aux_0),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value),LEAN_SCALAR_PTR_LITERAL(14, 50, 33, 106, 4, 142, 225, 217)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "pkgConfig"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65_value),LEAN_SCALAR_PTR_LITERAL(84, 166, 20, 31, 6, 123, 63, 83)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67_value;
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
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1_value),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Package"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 143, 146, 89, 89, 182, 160, 217)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(34, 23, 98, 66, 226, 155, 63, 223)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(178, 95, 147, 209, 102, 192, 116, 165)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(49, 159, 150, 51, 73, 206, 68, 246)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabPackageCommand"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(91, 182, 15, 92, 163, 165, 162, 240)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___boxed(lean_object*);
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "postUpdateDecl"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
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
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
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
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(253, 210, 120, 194, 116, 135, 247, 152)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_1),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_2),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_2),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_0),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_1),((lean_object*)&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
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
v___x_45_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_50_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_50_, 10, v___x_48_);
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
lean_object* v___x_67_; lean_object* v_env_68_; uint8_t v___x_69_; lean_object* v_env_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v_scopes_73_; lean_object* v___x_74_; lean_object* v_opts_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_67_ = lean_st_ref_get(v___y_65_);
v_env_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_ref(v_env_68_);
lean_dec(v___x_67_);
v___x_69_ = 0;
v_env_70_ = l_Lean_Environment_setRecordingDeps(v_env_68_, v___x_69_);
v___x_71_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_72_ = lean_st_ref_get(v___y_65_);
v_scopes_73_ = lean_ctor_get(v___x_72_, 2);
lean_inc(v_scopes_73_);
lean_dec(v___x_72_);
v___x_74_ = l_List_head_x21___redArg(v___x_71_, v_scopes_73_);
lean_dec(v_scopes_73_);
v_opts_75_ = lean_ctor_get(v___x_74_, 1);
lean_inc_ref(v_opts_75_);
lean_dec(v___x_74_);
v___x_76_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_77_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5);
v___x_78_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_78_, 0, v_env_70_);
lean_ctor_set(v___x_78_, 1, v___x_76_);
lean_ctor_set(v___x_78_, 2, v___x_77_);
lean_ctor_set(v___x_78_, 3, v_opts_75_);
v___x_79_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v_msgData_64_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msgData_81_, v___y_82_);
lean_dec(v___y_82_);
return v_res_84_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_box(1);
v___x_86_ = l_Lean_MessageData_ofFormat(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2));
v___x_91_ = l_Lean_MessageData_ofFormat(v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6(lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
return v_x_92_;
}
else
{
lean_object* v_head_94_; lean_object* v_tail_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_117_; 
v_head_94_ = lean_ctor_get(v_x_93_, 0);
v_tail_95_ = lean_ctor_get(v_x_93_, 1);
v_isSharedCheck_117_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_117_ == 0)
{
v___x_97_ = v_x_93_;
v_isShared_98_ = v_isSharedCheck_117_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_tail_95_);
lean_inc(v_head_94_);
lean_dec(v_x_93_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_117_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v_before_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_115_; 
v_before_99_ = lean_ctor_get(v_head_94_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v_head_94_);
if (v_isSharedCheck_115_ == 0)
{
lean_object* v_unused_116_; 
v_unused_116_ = lean_ctor_get(v_head_94_, 1);
lean_dec(v_unused_116_);
v___x_101_ = v_head_94_;
v_isShared_102_ = v_isSharedCheck_115_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_before_99_);
lean_dec(v_head_94_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_115_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0);
if (v_isShared_102_ == 0)
{
lean_ctor_set_tag(v___x_101_, 7);
lean_ctor_set(v___x_101_, 1, v___x_103_);
lean_ctor_set(v___x_101_, 0, v_x_92_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_x_92_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___x_103_);
v___x_105_ = v_reuseFailAlloc_114_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3);
if (v_isShared_98_ == 0)
{
lean_ctor_set_tag(v___x_97_, 7);
lean_ctor_set(v___x_97_, 1, v___x_106_);
lean_ctor_set(v___x_97_, 0, v___x_105_);
v___x_108_ = v___x_97_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v___x_106_);
v___x_108_ = v_reuseFailAlloc_113_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = l_Lean_MessageData_ofSyntax(v_before_99_);
v___x_110_ = l_Lean_indentD(v___x_109_);
v___x_111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_108_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v_x_92_ = v___x_111_;
v_x_93_ = v_tail_95_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(lean_object* v_opts_118_, lean_object* v_opt_119_){
_start:
{
lean_object* v_name_120_; lean_object* v_defValue_121_; lean_object* v_map_122_; lean_object* v___x_123_; 
v_name_120_ = lean_ctor_get(v_opt_119_, 0);
v_defValue_121_ = lean_ctor_get(v_opt_119_, 1);
v_map_122_ = lean_ctor_get(v_opts_118_, 0);
v___x_123_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_122_, v_name_120_);
if (lean_obj_tag(v___x_123_) == 0)
{
uint8_t v___x_124_; 
v___x_124_ = lean_unbox(v_defValue_121_);
return v___x_124_;
}
else
{
lean_object* v_val_125_; 
v_val_125_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_val_125_);
lean_dec_ref_known(v___x_123_, 1);
if (lean_obj_tag(v_val_125_) == 1)
{
uint8_t v_v_126_; 
v_v_126_ = lean_ctor_get_uint8(v_val_125_, 0);
lean_dec_ref_known(v_val_125_, 0);
return v_v_126_;
}
else
{
uint8_t v___x_127_; 
lean_dec(v_val_125_);
v___x_127_ = lean_unbox(v_defValue_121_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5___boxed(lean_object* v_opts_128_, lean_object* v_opt_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(v_opts_128_, v_opt_129_);
lean_dec_ref(v_opt_129_);
lean_dec_ref(v_opts_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_136_ = l_Lean_MessageData_ofFormat(v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_137_, lean_object* v_macroStack_138_, lean_object* v___y_139_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v_scopes_143_; lean_object* v___x_144_; lean_object* v_opts_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_141_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_142_ = lean_st_ref_get(v___y_139_);
v_scopes_143_ = lean_ctor_get(v___x_142_, 2);
lean_inc(v_scopes_143_);
lean_dec(v___x_142_);
v___x_144_ = l_List_head_x21___redArg(v___x_141_, v_scopes_143_);
lean_dec(v_scopes_143_);
v_opts_145_ = lean_ctor_get(v___x_144_, 1);
lean_inc_ref(v_opts_145_);
lean_dec(v___x_144_);
v___x_146_ = l_Lean_Elab_pp_macroStack;
v___x_147_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(v_opts_145_, v___x_146_);
lean_dec_ref(v_opts_145_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; 
lean_dec(v_macroStack_138_);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v_msgData_137_);
return v___x_148_;
}
else
{
if (lean_obj_tag(v_macroStack_138_) == 0)
{
lean_object* v___x_149_; 
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v_msgData_137_);
return v___x_149_;
}
else
{
lean_object* v_head_150_; lean_object* v_after_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_166_; 
v_head_150_ = lean_ctor_get(v_macroStack_138_, 0);
lean_inc(v_head_150_);
v_after_151_ = lean_ctor_get(v_head_150_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_head_150_);
if (v_isSharedCheck_166_ == 0)
{
lean_object* v_unused_167_; 
v_unused_167_ = lean_ctor_get(v_head_150_, 0);
lean_dec(v_unused_167_);
v___x_153_ = v_head_150_;
v_isShared_154_ = v_isSharedCheck_166_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_after_151_);
lean_dec(v_head_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_166_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0);
if (v_isShared_154_ == 0)
{
lean_ctor_set_tag(v___x_153_, 7);
lean_ctor_set(v___x_153_, 1, v___x_155_);
lean_ctor_set(v___x_153_, 0, v_msgData_137_);
v___x_157_ = v___x_153_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_msgData_137_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___x_155_);
v___x_157_ = v_reuseFailAlloc_165_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v_msgData_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_158_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = l_Lean_MessageData_ofSyntax(v_after_151_);
v___x_161_ = l_Lean_indentD(v___x_160_);
v_msgData_162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_162_, 0, v___x_159_);
lean_ctor_set(v_msgData_162_, 1, v___x_161_);
v___x_163_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6(v_msgData_162_, v_macroStack_138_);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_168_, lean_object* v_macroStack_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_168_, v_macroStack_169_, v___y_170_);
lean_dec(v___y_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(lean_object* v_msg_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Elab_Command_getRef___redArg(v___y_174_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v_macroStack_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_a_182_; lean_object* v___x_183_; lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_192_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v_macroStack_179_ = lean_ctor_get(v___y_174_, 4);
v___x_180_ = l_Lean_Elab_getBetterRef(v_a_178_, v_macroStack_179_);
lean_dec(v_a_178_);
v___x_181_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msg_173_, v___y_175_);
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref(v___x_181_);
lean_inc(v_macroStack_179_);
v___x_183_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_a_182_, v_macroStack_179_, v___y_175_);
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_192_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_180_);
lean_ctor_set(v___x_188_, 1, v_a_184_);
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 1);
lean_ctor_set(v___x_186_, 0, v___x_188_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref(v_msg_173_);
v_a_193_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_177_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_177_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg___boxed(lean_object* v_msg_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(lean_object* v_ref_206_, lean_object* v_msg_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Elab_Command_getRef___redArg(v___y_208_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v_fileName_213_; lean_object* v_fileMap_214_; lean_object* v_currRecDepth_215_; lean_object* v_cmdPos_216_; lean_object* v_macroStack_217_; lean_object* v_quotContext_x3f_218_; lean_object* v_currMacroScope_219_; lean_object* v_snap_x3f_220_; lean_object* v_cancelTk_x3f_221_; uint8_t v_suppressElabErrors_222_; uint8_t v_checkDeprecated_223_; lean_object* v_ref_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
v_fileName_213_ = lean_ctor_get(v___y_208_, 0);
v_fileMap_214_ = lean_ctor_get(v___y_208_, 1);
v_currRecDepth_215_ = lean_ctor_get(v___y_208_, 2);
v_cmdPos_216_ = lean_ctor_get(v___y_208_, 3);
v_macroStack_217_ = lean_ctor_get(v___y_208_, 4);
v_quotContext_x3f_218_ = lean_ctor_get(v___y_208_, 5);
v_currMacroScope_219_ = lean_ctor_get(v___y_208_, 6);
v_snap_x3f_220_ = lean_ctor_get(v___y_208_, 8);
v_cancelTk_x3f_221_ = lean_ctor_get(v___y_208_, 9);
v_suppressElabErrors_222_ = lean_ctor_get_uint8(v___y_208_, sizeof(void*)*10);
v_checkDeprecated_223_ = lean_ctor_get_uint8(v___y_208_, sizeof(void*)*10 + 1);
v_ref_224_ = l_Lean_replaceRef(v_ref_206_, v_a_212_);
lean_dec(v_a_212_);
lean_inc(v_cancelTk_x3f_221_);
lean_inc(v_snap_x3f_220_);
lean_inc(v_currMacroScope_219_);
lean_inc(v_quotContext_x3f_218_);
lean_inc(v_macroStack_217_);
lean_inc(v_cmdPos_216_);
lean_inc(v_currRecDepth_215_);
lean_inc_ref(v_fileMap_214_);
lean_inc_ref(v_fileName_213_);
v___x_225_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_225_, 0, v_fileName_213_);
lean_ctor_set(v___x_225_, 1, v_fileMap_214_);
lean_ctor_set(v___x_225_, 2, v_currRecDepth_215_);
lean_ctor_set(v___x_225_, 3, v_cmdPos_216_);
lean_ctor_set(v___x_225_, 4, v_macroStack_217_);
lean_ctor_set(v___x_225_, 5, v_quotContext_x3f_218_);
lean_ctor_set(v___x_225_, 6, v_currMacroScope_219_);
lean_ctor_set(v___x_225_, 7, v_ref_224_);
lean_ctor_set(v___x_225_, 8, v_snap_x3f_220_);
lean_ctor_set(v___x_225_, 9, v_cancelTk_x3f_221_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*10, v_suppressElabErrors_222_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*10 + 1, v_checkDeprecated_223_);
v___x_226_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_207_, v___x_225_, v___y_209_);
lean_dec_ref_known(v___x_225_, 10);
return v___x_226_;
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref(v_msg_207_);
v_a_227_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_211_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_211_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg___boxed(lean_object* v_ref_235_, lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_235_, v_msg_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v_ref_235_);
return v_res_240_;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Array_mkArray0___redArg();
return v___x_246_;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(lean_object* v_tyName_303_, lean_object* v_id_304_, lean_object* v_ty_305_, lean_object* v_config_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___x_392_; lean_object* v_whereInfo_394_; lean_object* v_fs_395_; lean_object* v_wds_x3f_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_392_ = l_Lake_PackageConfig_instConfigInfo;
v___x_417_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22));
lean_inc(v_config_306_);
v___x_418_ = l_Lean_Syntax_isOfKind(v_config_306_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_419_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_420_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_419_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = l_Lean_Syntax_getArg(v_config_306_, v___x_421_);
lean_inc(v___x_422_);
v___x_423_ = l_Lean_Syntax_matchesNull(v___x_422_, v___x_421_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_422_);
v___x_425_ = l_Lean_Syntax_matchesNull(v___x_422_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec(v___x_422_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_426_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_427_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_426_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_428_ = l_Lean_Syntax_getArg(v___x_422_, v___x_421_);
lean_dec(v___x_422_);
v___x_429_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26));
lean_inc(v___x_428_);
v___x_430_ = l_Lean_Syntax_isOfKind(v___x_428_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28));
lean_inc(v___x_428_);
v___x_432_ = l_Lean_Syntax_isOfKind(v___x_428_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v___x_428_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_433_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_434_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_433_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_435_ = l_Lean_Syntax_getArg(v___x_428_, v___x_421_);
v___x_436_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30));
lean_inc(v___x_435_);
v___x_437_ = l_Lean_Syntax_isOfKind(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v___x_435_);
lean_dec(v___x_428_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_438_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_439_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_438_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_440_ = l_Lean_Syntax_getArg(v___x_435_, v___x_424_);
v___x_441_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32));
lean_inc(v___x_440_);
v___x_442_ = l_Lean_Syntax_isOfKind(v___x_440_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v___x_440_);
lean_dec(v___x_435_);
lean_dec(v___x_428_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_443_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_444_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_443_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_444_;
}
else
{
lean_object* v_tk_445_; lean_object* v___x_446_; lean_object* v_wds_x3f_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_tk_445_ = l_Lean_Syntax_getArg(v___x_435_, v___x_421_);
lean_dec(v___x_435_);
v___x_446_ = l_Lean_Syntax_getArg(v___x_440_, v___x_421_);
lean_dec(v___x_440_);
v___x_454_ = l_Lean_Syntax_getArg(v___x_428_, v___x_424_);
lean_dec(v___x_428_);
v___x_455_ = l_Lean_Syntax_isNone(v___x_454_);
if (v___x_455_ == 0)
{
uint8_t v___x_456_; 
lean_inc(v___x_454_);
v___x_456_ = l_Lean_Syntax_matchesNull(v___x_454_, v___x_424_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v___x_454_);
lean_dec(v___x_446_);
lean_dec(v_tk_445_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_457_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_458_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_457_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_458_;
}
else
{
lean_object* v_wds_x3f_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_wds_x3f_459_ = l_Lean_Syntax_getArg(v___x_454_, v___x_421_);
lean_dec(v___x_454_);
v___x_460_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_459_);
v___x_461_ = l_Lean_Syntax_isOfKind(v_wds_x3f_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec(v_wds_x3f_459_);
lean_dec(v___x_446_);
lean_dec(v_tk_445_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_462_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_463_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_462_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_463_;
}
else
{
lean_object* v___x_464_; 
lean_dec(v_config_306_);
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v_wds_x3f_459_);
v_wds_x3f_448_ = v___x_464_;
v___y_449_ = v_a_307_;
v___y_450_ = v_a_308_;
goto v___jp_447_;
}
}
}
else
{
lean_object* v___x_465_; 
lean_dec(v___x_454_);
lean_dec(v_config_306_);
v___x_465_ = lean_box(0);
v_wds_x3f_448_ = v___x_465_;
v___y_449_ = v_a_307_;
v___y_450_ = v_a_308_;
goto v___jp_447_;
}
v___jp_447_:
{
lean_object* v_fs_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_fs_451_ = l_Lean_Syntax_getArgs(v___x_446_);
lean_dec(v___x_446_);
v___x_452_ = l_Lean_Syntax_getHeadInfo(v_tk_445_);
lean_dec(v_tk_445_);
v___x_453_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_451_);
lean_dec_ref(v_fs_451_);
v_whereInfo_394_ = v___x_452_;
v_fs_395_ = v___x_453_;
v_wds_x3f_396_ = v_wds_x3f_448_;
v___y_397_ = v___y_449_;
v___y_398_ = v___y_450_;
goto v___jp_393_;
}
}
}
}
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_466_ = l_Lean_Syntax_getArg(v___x_428_, v___x_424_);
v___x_467_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32));
lean_inc(v___x_466_);
v___x_468_ = l_Lean_Syntax_isOfKind(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v___x_466_);
lean_dec(v___x_428_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_469_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_470_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_469_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_470_;
}
else
{
lean_object* v_tk_471_; lean_object* v___x_472_; lean_object* v_wds_x3f_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_tk_471_ = l_Lean_Syntax_getArg(v___x_428_, v___x_421_);
v___x_472_ = l_Lean_Syntax_getArg(v___x_466_, v___x_421_);
lean_dec(v___x_466_);
v___x_480_ = lean_unsigned_to_nat(2u);
v___x_481_ = l_Lean_Syntax_getArg(v___x_428_, v___x_480_);
lean_dec(v___x_428_);
v___x_482_ = l_Lean_Syntax_isNone(v___x_481_);
if (v___x_482_ == 0)
{
uint8_t v___x_483_; 
lean_inc(v___x_481_);
v___x_483_ = l_Lean_Syntax_matchesNull(v___x_481_, v___x_424_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v___x_481_);
lean_dec(v___x_472_);
lean_dec(v_tk_471_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_484_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_485_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_484_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_485_;
}
else
{
lean_object* v_wds_x3f_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_wds_x3f_486_ = l_Lean_Syntax_getArg(v___x_481_, v___x_421_);
lean_dec(v___x_481_);
v___x_487_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_486_);
v___x_488_ = l_Lean_Syntax_isOfKind(v_wds_x3f_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v_wds_x3f_486_);
lean_dec(v___x_472_);
lean_dec(v_tk_471_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_489_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_490_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_489_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; 
lean_dec(v_config_306_);
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v_wds_x3f_486_);
v_wds_x3f_474_ = v___x_491_;
v___y_475_ = v_a_307_;
v___y_476_ = v_a_308_;
goto v___jp_473_;
}
}
}
else
{
lean_object* v___x_492_; 
lean_dec(v___x_481_);
lean_dec(v_config_306_);
v___x_492_ = lean_box(0);
v_wds_x3f_474_ = v___x_492_;
v___y_475_ = v_a_307_;
v___y_476_ = v_a_308_;
goto v___jp_473_;
}
v___jp_473_:
{
lean_object* v_fs_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_fs_477_ = l_Lean_Syntax_getArgs(v___x_472_);
lean_dec(v___x_472_);
v___x_478_ = l_Lean_Syntax_getHeadInfo(v_tk_471_);
lean_dec(v_tk_471_);
v___x_479_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_477_);
lean_dec_ref(v_fs_477_);
v_whereInfo_394_ = v___x_478_;
v_fs_395_ = v___x_479_;
v_wds_x3f_396_ = v_wds_x3f_474_;
v___y_397_ = v___y_475_;
v___y_398_ = v___y_476_;
goto v___jp_393_;
}
}
}
}
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v___x_422_);
lean_dec(v_config_306_);
v___x_493_ = lean_box(2);
v___x_494_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
v___x_495_ = lean_box(0);
v_whereInfo_394_ = v___x_493_;
v_fs_395_ = v___x_494_;
v_wds_x3f_396_ = v___x_495_;
v___y_397_ = v_a_307_;
v___y_398_ = v_a_308_;
goto v___jp_393_;
}
}
v___jp_310_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_317_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_312_, 5);
lean_inc_ref_n(v___y_315_, 6);
lean_inc_ref_n(v___y_313_, 6);
v___x_318_ = l_Lean_Name_mkStr4(v___y_313_, v___y_315_, v___y_312_, v___x_317_);
v___x_319_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_320_ = l_Lean_Name_mkStr4(v___y_313_, v___y_315_, v___y_312_, v___x_319_);
v___x_321_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_322_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___y_311_, 8);
v___x_323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_323_, 0, v___y_311_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_322_);
lean_inc_ref_n(v___x_323_, 8);
v___x_324_ = l_Lean_Syntax_node7(v___y_311_, v___x_320_, v___x_323_, v___x_323_, v___x_323_, v___x_323_, v___x_323_, v___x_323_, v___x_323_);
v___x_325_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5));
v___x_326_ = l_Lean_Name_mkStr4(v___y_313_, v___y_315_, v___y_312_, v___x_325_);
v___x_327_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6));
v___x_328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_328_, 0, v___y_311_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_330_ = l_Lean_Name_mkStr4(v___y_313_, v___y_315_, v___y_312_, v___x_329_);
v___x_331_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
lean_inc_n(v___y_316_, 2);
v___x_332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_332_, 0, v___y_316_);
lean_ctor_set(v___x_332_, 1, v___x_321_);
lean_ctor_set(v___x_332_, 2, v___x_331_);
v___x_333_ = lean_unsigned_to_nat(2u);
v___x_334_ = lean_mk_empty_array_with_capacity(v___x_333_);
v___x_335_ = lean_array_push(v___x_334_, v_id_304_);
v___x_336_ = lean_array_push(v___x_335_, v___x_332_);
v___x_337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_337_, 0, v___y_316_);
lean_ctor_set(v___x_337_, 1, v___x_330_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
v___x_338_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_339_ = l_Lean_Name_mkStr4(v___y_313_, v___y_315_, v___y_312_, v___x_338_);
v___x_340_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_341_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_342_ = l_Lean_Name_mkStr4(v___y_313_, v___y_315_, v___x_340_, v___x_341_);
v___x_343_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_344_, 0, v___y_311_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_Syntax_node2(v___y_311_, v___x_342_, v___x_344_, v_ty_305_);
v___x_346_ = l_Lean_Syntax_node1(v___y_311_, v___x_321_, v___x_345_);
v___x_347_ = l_Lean_Syntax_node2(v___y_311_, v___x_339_, v___x_323_, v___x_346_);
v___x_348_ = l_Lean_Syntax_node5(v___y_311_, v___x_326_, v___x_328_, v___x_337_, v___x_347_, v___y_314_, v___x_323_);
v___x_349_ = l_Lean_Syntax_node2(v___y_311_, v___x_318_, v___x_324_, v___x_348_);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
v___jp_351_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_361_ = l_Lean_mkOptionalNode(v___y_360_);
v___x_362_ = lean_unsigned_to_nat(3u);
v___x_363_ = lean_mk_empty_array_with_capacity(v___x_362_);
v___x_364_ = lean_array_push(v___x_363_, v___y_353_);
v___x_365_ = lean_array_push(v___x_364_, v___y_359_);
v___x_366_ = lean_array_push(v___x_365_, v___x_361_);
v___x_367_ = lean_box(2);
lean_inc(v___y_354_);
v___x_368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v___y_354_);
lean_ctor_set(v___x_368_, 2, v___x_366_);
v___x_369_ = l_Lean_Elab_Command_getRef___redArg(v___y_352_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref_known(v___x_369_, 1);
v___x_371_ = 0;
v___x_372_ = l_Lean_SourceInfo_fromRef(v_a_370_, v___x_371_);
lean_dec(v_a_370_);
v___x_373_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_352_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_quotContext_x3f_374_; 
lean_dec_ref_known(v___x_373_, 1);
v_quotContext_x3f_374_ = lean_ctor_get(v___y_352_, 5);
if (lean_obj_tag(v_quotContext_x3f_374_) == 0)
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_357_);
lean_dec_ref(v___x_375_);
v___y_311_ = v___x_372_;
v___y_312_ = v___y_356_;
v___y_313_ = v___y_355_;
v___y_314_ = v___x_368_;
v___y_315_ = v___y_358_;
v___y_316_ = v___x_367_;
goto v___jp_310_;
}
else
{
v___y_311_ = v___x_372_;
v___y_312_ = v___y_356_;
v___y_313_ = v___y_355_;
v___y_314_ = v___x_368_;
v___y_315_ = v___y_358_;
v___y_316_ = v___x_367_;
goto v___jp_310_;
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v___x_372_);
lean_dec_ref_known(v___x_368_, 3);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
v_a_376_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_373_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_373_);
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
lean_dec_ref_known(v___x_368_, 3);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
v_a_384_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_369_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_369_);
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
lean_object* v_fieldMap_399_; lean_object* v___x_400_; lean_object* v_whereTk_401_; lean_object* v___x_402_; 
v_fieldMap_399_ = lean_ctor_get(v___x_392_, 1);
v___x_400_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13));
v_whereTk_401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_whereTk_401_, 0, v_whereInfo_394_);
lean_ctor_set(v_whereTk_401_, 1, v___x_400_);
v___x_402_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_303_, v_fieldMap_399_, v_fs_395_, v___y_397_, v___y_398_);
lean_dec_ref(v_fs_395_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
v___x_404_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_405_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_406_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_407_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18));
if (lean_obj_tag(v_wds_x3f_396_) == 0)
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
v___y_352_ = v___y_397_;
v___y_353_ = v_whereTk_401_;
v___y_354_ = v___x_407_;
v___y_355_ = v___x_404_;
v___y_356_ = v___x_406_;
v___y_357_ = v___y_398_;
v___y_358_ = v___x_405_;
v___y_359_ = v_a_403_;
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
v___y_352_ = v___y_397_;
v___y_353_ = v_whereTk_401_;
v___y_354_ = v___x_407_;
v___y_355_ = v___x_404_;
v___y_356_ = v___x_406_;
v___y_357_ = v___y_398_;
v___y_358_ = v___x_405_;
v___y_359_ = v_a_403_;
v___y_360_ = v___x_414_;
goto v___jp_351_;
}
}
}
}
else
{
lean_dec_ref_known(v_whereTk_401_, 2);
lean_dec(v_wds_x3f_396_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___boxed(lean_object* v_tyName_496_, lean_object* v_id_497_, lean_object* v_ty_498_, lean_object* v_config_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v_tyName_496_, v_id_497_, v_ty_498_, v_config_499_, v_a_500_, v_a_501_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
return v_res_503_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13));
v___x_526_ = l_Lean_stringToMessageData(v___x_525_);
return v___x_526_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20));
v___x_536_ = l_String_toRawSubstring_x27(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35));
v___x_559_ = l_String_toRawSubstring_x27(v___x_558_);
return v___x_559_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41));
v___x_567_ = l_String_toRawSubstring_x27(v___x_566_);
return v___x_567_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44));
v___x_572_ = l_String_toRawSubstring_x27(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47));
v___x_577_ = l_String_toRawSubstring_x27(v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56));
v___x_588_ = l_String_toRawSubstring_x27(v___x_587_);
return v___x_588_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65));
v___x_604_ = l_String_toRawSubstring_x27(v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(lean_object* v_stx_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12));
lean_inc(v_stx_607_);
v___x_680_ = l_Lean_Syntax_isOfKind(v_stx_607_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
v___x_682_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_607_, v___x_681_, v_a_608_, v_a_609_);
lean_dec(v_stx_607_);
return v___x_682_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; uint8_t v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; uint8_t v___y_817_; lean_object* v_a_818_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; uint8_t v___y_850_; lean_object* v_a_851_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; uint8_t v___y_948_; lean_object* v___y_949_; lean_object* v_a_950_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; uint8_t v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; uint8_t v___y_1072_; lean_object* v___y_1073_; lean_object* v_a_1074_; lean_object* v_kw_1101_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v_nameStx_x3f_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_box(0);
v___x_685_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15));
v___x_686_ = l_Lean_Syntax_getArg(v_stx_607_, v___x_683_);
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = l_Lean_Syntax_getArg(v_stx_607_, v___x_687_);
v___x_689_ = lean_unsigned_to_nat(2u);
v_kw_1101_ = l_Lean_Syntax_getArg(v_stx_607_, v___x_689_);
v___x_1190_ = lean_unsigned_to_nat(3u);
v___x_1191_ = l_Lean_Syntax_getArg(v_stx_607_, v___x_1190_);
v___x_1192_ = l_Lean_Syntax_isNone(v___x_1191_);
if (v___x_1192_ == 0)
{
uint8_t v___x_1193_; 
lean_inc(v___x_1191_);
v___x_1193_ = l_Lean_Syntax_matchesNull(v___x_1191_, v___x_687_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec(v___x_1191_);
lean_dec(v_kw_1101_);
lean_dec(v___x_688_);
lean_dec(v___x_686_);
v___x_1194_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
v___x_1195_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_607_, v___x_1194_, v_a_608_, v_a_609_);
lean_dec(v_stx_607_);
return v___x_1195_;
}
else
{
lean_object* v_nameStx_x3f_1196_; lean_object* v___x_1197_; 
v_nameStx_x3f_1196_ = l_Lean_Syntax_getArg(v___x_1191_, v___x_683_);
lean_dec(v___x_1191_);
v___x_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_nameStx_x3f_1196_);
v_nameStx_x3f_1175_ = v___x_1197_;
v___y_1176_ = v_a_608_;
v___y_1177_ = v_a_609_;
goto v___jp_1174_;
}
}
else
{
lean_object* v___x_1198_; 
lean_dec(v___x_1191_);
v___x_1198_ = lean_box(0);
v_nameStx_x3f_1175_ = v___x_1198_;
v___y_1176_ = v_a_608_;
v___y_1177_ = v_a_609_;
goto v___jp_1174_;
}
v___jp_690_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_inc_ref_n(v___y_713_, 3);
v___x_717_ = l_Array_append___redArg(v___y_713_, v___y_716_);
lean_dec_ref(v___y_716_);
lean_inc_n(v___y_712_, 6);
lean_inc_n(v___y_705_, 18);
v___x_718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_718_, 0, v___y_705_);
lean_ctor_set(v___x_718_, 1, v___y_712_);
lean_ctor_set(v___x_718_, 2, v___x_717_);
v___x_719_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16));
lean_inc_ref(v___y_698_);
lean_inc_ref_n(v___y_701_, 6);
lean_inc_ref_n(v___y_707_, 7);
v___x_720_ = l_Lean_Name_mkStr4(v___y_707_, v___y_701_, v___y_698_, v___x_719_);
v___x_721_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17));
v___x_722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_722_, 0, v___y_705_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
lean_inc_ref(v___y_714_);
v___x_723_ = l_Lean_Syntax_SepArray_ofElems(v___y_714_, v___y_695_);
lean_dec_ref(v___y_695_);
v___x_724_ = l_Array_append___redArg(v___y_713_, v___x_723_);
lean_dec_ref(v___x_723_);
v___x_725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_725_, 0, v___y_705_);
lean_ctor_set(v___x_725_, 1, v___y_712_);
lean_ctor_set(v___x_725_, 2, v___x_724_);
v___x_726_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18));
v___x_727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_727_, 0, v___y_705_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
lean_inc(v___x_720_);
v___x_728_ = l_Lean_Syntax_node3(v___y_705_, v___x_720_, v___x_722_, v___x_725_, v___x_727_);
v___x_729_ = l_Lean_Syntax_node1(v___y_705_, v___y_712_, v___x_728_);
v___x_730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_730_, 0, v___y_705_);
lean_ctor_set(v___x_730_, 1, v___y_712_);
lean_ctor_set(v___x_730_, 2, v___y_713_);
lean_inc_ref_n(v___x_730_, 8);
lean_inc(v___y_692_);
v___x_731_ = l_Lean_Syntax_node7(v___y_705_, v___y_692_, v___x_718_, v___x_729_, v___x_730_, v___x_730_, v___x_730_, v___x_730_, v___x_730_);
v___x_732_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19));
lean_inc_ref_n(v___y_711_, 3);
v___x_733_ = l_Lean_Name_mkStr4(v___y_707_, v___y_701_, v___y_711_, v___x_732_);
v___x_734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_734_, 0, v___y_705_);
lean_ctor_set(v___x_734_, 1, v___x_732_);
v___x_735_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_736_ = l_Lean_Name_mkStr4(v___y_707_, v___y_701_, v___y_711_, v___x_735_);
v___x_737_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
lean_inc_n(v___y_703_, 2);
v___x_738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_738_, 0, v___y_703_);
lean_ctor_set(v___x_738_, 1, v___y_712_);
lean_ctor_set(v___x_738_, 2, v___x_737_);
v___x_739_ = lean_mk_empty_array_with_capacity(v___x_689_);
lean_inc(v___y_704_);
lean_inc_ref(v___x_739_);
v___x_740_ = lean_array_push(v___x_739_, v___y_704_);
lean_inc_ref(v___x_738_);
v___x_741_ = lean_array_push(v___x_740_, v___x_738_);
lean_inc(v___x_736_);
v___x_742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_742_, 0, v___y_703_);
lean_ctor_set(v___x_742_, 1, v___x_736_);
lean_ctor_set(v___x_742_, 2, v___x_741_);
v___x_743_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_744_ = l_Lean_Name_mkStr4(v___y_707_, v___y_701_, v___y_711_, v___x_743_);
v___x_745_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_746_ = l_Lean_Name_mkStr4(v___y_707_, v___y_701_, v___y_698_, v___x_745_);
v___x_747_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_748_, 0, v___y_705_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21);
v___x_750_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22));
v___x_751_ = l_Lean_addMacroScope(v___y_699_, v___x_750_, v___y_710_);
v___x_752_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24));
v___x_753_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25));
lean_inc(v___y_706_);
v___x_754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___y_706_);
v___x_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_752_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_756_, 0, v___y_705_);
lean_ctor_set(v___x_756_, 1, v___x_749_);
lean_ctor_set(v___x_756_, 2, v___x_751_);
lean_ctor_set(v___x_756_, 3, v___x_755_);
v___x_757_ = l_Lean_Syntax_node2(v___y_705_, v___x_746_, v___x_748_, v___x_756_);
v___x_758_ = l_Lean_Syntax_node1(v___y_705_, v___y_712_, v___x_757_);
lean_inc(v___x_744_);
v___x_759_ = l_Lean_Syntax_node2(v___y_705_, v___x_744_, v___x_730_, v___x_758_);
v___x_760_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26));
v___x_761_ = l_Lean_Name_mkStr4(v___y_707_, v___y_701_, v___y_711_, v___x_760_);
lean_inc_ref(v___y_702_);
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v___y_705_);
lean_ctor_set(v___x_762_, 1, v___y_702_);
v___x_763_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27));
v___x_764_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___x_765_ = l_Lean_Name_mkStr4(v___y_707_, v___y_701_, v___x_763_, v___x_764_);
lean_inc(v___x_765_);
v___x_766_ = l_Lean_Syntax_node2(v___y_705_, v___x_765_, v___x_730_, v___x_730_);
lean_inc(v___x_761_);
v___x_767_ = l_Lean_Syntax_node4(v___y_705_, v___x_761_, v___x_762_, v___y_708_, v___x_766_, v___x_730_);
lean_inc(v___x_733_);
v___x_768_ = l_Lean_Syntax_node4(v___y_705_, v___x_733_, v___x_734_, v___x_742_, v___x_759_, v___x_767_);
lean_inc(v___y_694_);
v___x_769_ = l_Lean_Syntax_node2(v___y_705_, v___y_694_, v___x_731_, v___x_768_);
lean_inc(v___x_769_);
v___x_770_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_770_, 0, v___x_769_);
v___x_771_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_stx_607_, v___x_769_, v___x_770_, v___y_715_, v___y_709_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec_ref_known(v___x_771_, 1);
v___x_772_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
v___x_773_ = l_Lean_Name_str___override(v___y_693_, v___x_772_);
v___x_774_ = l_Lean_mkIdentFrom(v___y_704_, v___x_773_, v___y_700_);
lean_dec(v___y_704_);
v___x_775_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_715_, v___y_709_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_777_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_715_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_dec_ref_known(v___x_777_, 1);
if (lean_obj_tag(v___y_696_) == 0)
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_709_);
lean_dec_ref(v___x_778_);
v___y_612_ = v___y_702_;
v___y_613_ = v___y_691_;
v___y_614_ = v___y_703_;
v___y_615_ = v___x_739_;
v___y_616_ = v___x_721_;
v___y_617_ = v___y_692_;
v___y_618_ = v_a_776_;
v___y_619_ = v___x_732_;
v___y_620_ = v___x_761_;
v___y_621_ = v___x_744_;
v___y_622_ = v___y_707_;
v___y_623_ = v___y_694_;
v___y_624_ = v___x_733_;
v___y_625_ = v___y_709_;
v___y_626_ = v___y_712_;
v___y_627_ = v___x_720_;
v___y_628_ = v___y_713_;
v___y_629_ = v___y_697_;
v___y_630_ = v___x_726_;
v___y_631_ = v___y_715_;
v___y_632_ = v___x_738_;
v___y_633_ = v___x_736_;
v___y_634_ = v___x_774_;
v___y_635_ = v___x_765_;
goto v___jp_611_;
}
else
{
lean_dec_ref_known(v___y_696_, 1);
v___y_612_ = v___y_702_;
v___y_613_ = v___y_691_;
v___y_614_ = v___y_703_;
v___y_615_ = v___x_739_;
v___y_616_ = v___x_721_;
v___y_617_ = v___y_692_;
v___y_618_ = v_a_776_;
v___y_619_ = v___x_732_;
v___y_620_ = v___x_761_;
v___y_621_ = v___x_744_;
v___y_622_ = v___y_707_;
v___y_623_ = v___y_694_;
v___y_624_ = v___x_733_;
v___y_625_ = v___y_709_;
v___y_626_ = v___y_712_;
v___y_627_ = v___x_720_;
v___y_628_ = v___y_713_;
v___y_629_ = v___y_697_;
v___y_630_ = v___x_726_;
v___y_631_ = v___y_715_;
v___y_632_ = v___x_738_;
v___y_633_ = v___x_736_;
v___y_634_ = v___x_774_;
v___y_635_ = v___x_765_;
goto v___jp_611_;
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec(v_a_776_);
lean_dec(v___x_774_);
lean_dec(v___x_765_);
lean_dec(v___x_761_);
lean_dec(v___x_744_);
lean_dec_ref(v___x_739_);
lean_dec_ref_known(v___x_738_, 3);
lean_dec(v___x_736_);
lean_dec(v___x_733_);
lean_dec(v___x_720_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_703_);
lean_dec(v___y_697_);
lean_dec(v___y_696_);
lean_dec(v___y_694_);
lean_dec(v___y_692_);
lean_dec(v___y_691_);
v_a_779_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_777_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_777_);
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
lean_dec(v___x_774_);
lean_dec(v___x_765_);
lean_dec(v___x_761_);
lean_dec(v___x_744_);
lean_dec_ref(v___x_739_);
lean_dec_ref_known(v___x_738_, 3);
lean_dec(v___x_736_);
lean_dec(v___x_733_);
lean_dec(v___x_720_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_703_);
lean_dec(v___y_697_);
lean_dec(v___y_696_);
lean_dec(v___y_694_);
lean_dec(v___y_692_);
lean_dec(v___y_691_);
v_a_787_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_775_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_775_);
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
lean_dec(v___x_765_);
lean_dec(v___x_761_);
lean_dec(v___x_744_);
lean_dec_ref(v___x_739_);
lean_dec_ref_known(v___x_738_, 3);
lean_dec(v___x_736_);
lean_dec(v___x_733_);
lean_dec(v___x_720_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_704_);
lean_dec(v___y_703_);
lean_dec(v___y_697_);
lean_dec(v___y_696_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
lean_dec(v___y_692_);
lean_dec(v___y_691_);
return v___x_771_;
}
}
v___jp_795_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_819_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_820_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_796_, 2);
lean_inc_ref_n(v___y_805_, 2);
v___x_821_ = l_Lean_Name_mkStr4(v___y_805_, v___y_796_, v___x_819_, v___x_820_);
v___x_822_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_823_ = l_Lean_Name_mkStr4(v___y_805_, v___y_796_, v___x_819_, v___x_822_);
if (lean_obj_tag(v___y_803_) == 1)
{
lean_object* v_val_824_; lean_object* v___x_825_; 
v_val_824_ = lean_ctor_get(v___y_803_, 0);
lean_inc(v_val_824_);
lean_dec_ref_known(v___y_803_, 1);
v___x_825_ = l_Array_mkArray1___redArg(v_val_824_);
v___y_691_ = v___y_798_;
v___y_692_ = v___x_823_;
v___y_693_ = v___y_802_;
v___y_694_ = v___x_821_;
v___y_695_ = v___y_810_;
v___y_696_ = v___y_811_;
v___y_697_ = v___y_813_;
v___y_698_ = v___y_814_;
v___y_699_ = v_a_818_;
v___y_700_ = v___y_817_;
v___y_701_ = v___y_796_;
v___y_702_ = v___y_797_;
v___y_703_ = v___y_799_;
v___y_704_ = v___y_800_;
v___y_705_ = v___y_801_;
v___y_706_ = v___y_804_;
v___y_707_ = v___y_805_;
v___y_708_ = v___y_806_;
v___y_709_ = v___y_807_;
v___y_710_ = v___y_808_;
v___y_711_ = v___x_819_;
v___y_712_ = v___y_809_;
v___y_713_ = v___y_812_;
v___y_714_ = v___y_815_;
v___y_715_ = v___y_816_;
v___y_716_ = v___x_825_;
goto v___jp_690_;
}
else
{
lean_object* v___x_826_; 
lean_dec(v___y_803_);
v___x_826_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_691_ = v___y_798_;
v___y_692_ = v___x_823_;
v___y_693_ = v___y_802_;
v___y_694_ = v___x_821_;
v___y_695_ = v___y_810_;
v___y_696_ = v___y_811_;
v___y_697_ = v___y_813_;
v___y_698_ = v___y_814_;
v___y_699_ = v_a_818_;
v___y_700_ = v___y_817_;
v___y_701_ = v___y_796_;
v___y_702_ = v___y_797_;
v___y_703_ = v___y_799_;
v___y_704_ = v___y_800_;
v___y_705_ = v___y_801_;
v___y_706_ = v___y_804_;
v___y_707_ = v___y_805_;
v___y_708_ = v___y_806_;
v___y_709_ = v___y_807_;
v___y_710_ = v___y_808_;
v___y_711_ = v___x_819_;
v___y_712_ = v___y_809_;
v___y_713_ = v___y_812_;
v___y_714_ = v___y_815_;
v___y_715_ = v___y_816_;
v___y_716_ = v___x_826_;
goto v___jp_690_;
}
}
v___jp_827_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_852_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31));
lean_inc_ref_n(v___y_848_, 6);
lean_inc_ref_n(v___y_828_, 6);
lean_inc_ref_n(v___y_837_, 6);
v___x_853_ = l_Lean_Name_mkStr4(v___y_837_, v___y_828_, v___y_848_, v___x_852_);
v___x_854_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32));
lean_inc_n(v___y_846_, 28);
v___x_855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_855_, 0, v___y_846_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
lean_inc_ref(v___y_844_);
lean_inc_n(v___y_841_, 6);
v___x_856_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_856_, 0, v___y_846_);
lean_ctor_set(v___x_856_, 1, v___y_841_);
lean_ctor_set(v___x_856_, 2, v___y_844_);
v___x_857_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31));
v___x_858_ = l_Lean_Name_mkStr4(v___y_837_, v___y_828_, v___y_848_, v___x_857_);
v___x_859_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33));
v___x_860_ = l_Lean_Name_mkStr4(v___y_837_, v___y_828_, v___y_848_, v___x_859_);
v___x_861_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34));
v___x_862_ = l_Lean_Name_mkStr4(v___y_837_, v___y_828_, v___y_848_, v___x_861_);
v___x_863_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36);
v___x_864_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37));
lean_inc_n(v___y_842_, 3);
lean_inc_n(v_a_851_, 3);
v___x_865_ = l_Lean_addMacroScope(v_a_851_, v___x_864_, v___y_842_);
lean_inc_n(v___y_836_, 4);
v___x_866_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_866_, 0, v___y_846_);
lean_ctor_set(v___x_866_, 1, v___x_863_);
lean_ctor_set(v___x_866_, 2, v___x_865_);
lean_ctor_set(v___x_866_, 3, v___y_836_);
lean_inc_ref_n(v___x_856_, 18);
lean_inc_n(v___x_862_, 3);
v___x_867_ = l_Lean_Syntax_node2(v___y_846_, v___x_862_, v___x_866_, v___x_856_);
v___x_868_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38));
v___x_869_ = l_Lean_Name_mkStr4(v___y_837_, v___y_828_, v___y_848_, v___x_868_);
v___x_870_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39));
v___x_871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_871_, 0, v___y_846_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
lean_inc_ref_n(v___x_871_, 3);
lean_inc_n(v___x_869_, 3);
v___x_872_ = l_Lean_Syntax_node3(v___y_846_, v___x_869_, v___x_871_, v___x_856_, v___y_847_);
v___x_873_ = l_Lean_Syntax_node3(v___y_846_, v___y_841_, v___x_856_, v___x_856_, v___x_872_);
lean_inc_n(v___x_860_, 3);
v___x_874_ = l_Lean_Syntax_node2(v___y_846_, v___x_860_, v___x_867_, v___x_873_);
v___x_875_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40));
v___x_876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_876_, 0, v___y_846_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42);
v___x_878_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43));
v___x_879_ = l_Lean_addMacroScope(v_a_851_, v___x_878_, v___y_842_);
v___x_880_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_880_, 0, v___y_846_);
lean_ctor_set(v___x_880_, 1, v___x_877_);
lean_ctor_set(v___x_880_, 2, v___x_879_);
lean_ctor_set(v___x_880_, 3, v___y_836_);
v___x_881_ = l_Lean_Syntax_node2(v___y_846_, v___x_862_, v___x_880_, v___x_856_);
v___x_882_ = l_Lean_Syntax_node3(v___y_846_, v___x_869_, v___x_871_, v___x_856_, v___y_838_);
v___x_883_ = l_Lean_Syntax_node3(v___y_846_, v___y_841_, v___x_856_, v___x_856_, v___x_882_);
v___x_884_ = l_Lean_Syntax_node2(v___y_846_, v___x_860_, v___x_881_, v___x_883_);
v___x_885_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45);
v___x_886_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46));
v___x_887_ = l_Lean_addMacroScope(v_a_851_, v___x_886_, v___y_842_);
v___x_888_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_888_, 0, v___y_846_);
lean_ctor_set(v___x_888_, 1, v___x_885_);
lean_ctor_set(v___x_888_, 2, v___x_887_);
lean_ctor_set(v___x_888_, 3, v___y_836_);
v___x_889_ = l_Lean_Syntax_node2(v___y_846_, v___x_862_, v___x_888_, v___x_856_);
v___x_890_ = l_Lean_Syntax_node3(v___y_846_, v___x_869_, v___x_871_, v___x_856_, v___y_833_);
v___x_891_ = l_Lean_Syntax_node3(v___y_846_, v___y_841_, v___x_856_, v___x_856_, v___x_890_);
v___x_892_ = l_Lean_Syntax_node2(v___y_846_, v___x_860_, v___x_889_, v___x_891_);
v___x_893_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48);
v___x_894_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49));
v___x_895_ = l_Lean_addMacroScope(v_a_851_, v___x_894_, v___y_842_);
v___x_896_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_896_, 0, v___y_846_);
lean_ctor_set(v___x_896_, 1, v___x_893_);
lean_ctor_set(v___x_896_, 2, v___x_895_);
lean_ctor_set(v___x_896_, 3, v___y_836_);
v___x_897_ = l_Lean_Syntax_node2(v___y_846_, v___x_862_, v___x_896_, v___x_856_);
v___x_898_ = l_Lean_Syntax_node3(v___y_846_, v___x_869_, v___x_871_, v___x_856_, v___y_835_);
v___x_899_ = l_Lean_Syntax_node3(v___y_846_, v___y_841_, v___x_856_, v___x_856_, v___x_898_);
v___x_900_ = l_Lean_Syntax_node2(v___y_846_, v___x_860_, v___x_897_, v___x_899_);
lean_inc_ref_n(v___x_876_, 2);
v___x_901_ = l_Lean_Syntax_node7(v___y_846_, v___y_841_, v___x_874_, v___x_876_, v___x_884_, v___x_876_, v___x_892_, v___x_876_, v___x_900_);
v___x_902_ = l_Lean_Syntax_node1(v___y_846_, v___x_858_, v___x_901_);
v___x_903_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50));
v___x_904_ = l_Lean_Name_mkStr4(v___y_837_, v___y_828_, v___y_848_, v___x_903_);
v___x_905_ = l_Lean_Syntax_node1(v___y_846_, v___x_904_, v___x_856_);
v___x_906_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51));
v___x_907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_907_, 0, v___y_846_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Lean_Syntax_node6(v___y_846_, v___x_853_, v___x_855_, v___x_856_, v___x_902_, v___x_905_, v___x_856_, v___x_907_);
v___x_909_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_849_, v___y_839_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_911_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_909_, 1);
v___x_911_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_849_);
if (lean_obj_tag(v___x_911_) == 0)
{
if (lean_obj_tag(v___y_843_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v_a_914_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_839_);
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v___x_913_);
v___y_796_ = v___y_828_;
v___y_797_ = v___x_870_;
v___y_798_ = v___y_829_;
v___y_799_ = v___y_830_;
v___y_800_ = v___y_831_;
v___y_801_ = v_a_910_;
v___y_802_ = v___y_832_;
v___y_803_ = v___y_834_;
v___y_804_ = v___y_836_;
v___y_805_ = v___y_837_;
v___y_806_ = v___x_908_;
v___y_807_ = v___y_839_;
v___y_808_ = v_a_912_;
v___y_809_ = v___y_841_;
v___y_810_ = v___y_840_;
v___y_811_ = v___y_843_;
v___y_812_ = v___y_844_;
v___y_813_ = v___y_845_;
v___y_814_ = v___y_848_;
v___y_815_ = v___x_875_;
v___y_816_ = v___y_849_;
v___y_817_ = v___y_850_;
v_a_818_ = v_a_914_;
goto v___jp_795_;
}
else
{
lean_object* v_a_915_; lean_object* v_val_916_; 
v_a_915_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_911_, 1);
v_val_916_ = lean_ctor_get(v___y_843_, 0);
lean_inc(v_val_916_);
v___y_796_ = v___y_828_;
v___y_797_ = v___x_870_;
v___y_798_ = v___y_829_;
v___y_799_ = v___y_830_;
v___y_800_ = v___y_831_;
v___y_801_ = v_a_910_;
v___y_802_ = v___y_832_;
v___y_803_ = v___y_834_;
v___y_804_ = v___y_836_;
v___y_805_ = v___y_837_;
v___y_806_ = v___x_908_;
v___y_807_ = v___y_839_;
v___y_808_ = v_a_915_;
v___y_809_ = v___y_841_;
v___y_810_ = v___y_840_;
v___y_811_ = v___y_843_;
v___y_812_ = v___y_844_;
v___y_813_ = v___y_845_;
v___y_814_ = v___y_848_;
v___y_815_ = v___x_875_;
v___y_816_ = v___y_849_;
v___y_817_ = v___y_850_;
v_a_818_ = v_val_916_;
goto v___jp_795_;
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_a_910_);
lean_dec(v___x_908_);
lean_dec_ref(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_845_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_834_);
lean_dec(v___y_832_);
lean_dec(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v_stx_607_);
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
lean_dec_ref(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_845_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_834_);
lean_dec(v___y_832_);
lean_dec(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v_stx_607_);
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
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_951_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_952_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_953_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52));
lean_inc_ref_n(v___y_941_, 3);
v___x_954_ = l_Lean_Name_mkStr4(v___y_941_, v___x_951_, v___x_952_, v___x_953_);
v___x_955_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53));
v___x_956_ = l_Lean_Name_mkStr4(v___y_941_, v___x_951_, v___x_952_, v___x_955_);
v___x_957_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_958_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___y_943_, 4);
v___x_959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_959_, 0, v___y_943_);
lean_ctor_set(v___x_959_, 1, v___x_957_);
lean_ctor_set(v___x_959_, 2, v___x_958_);
lean_inc_ref(v___x_959_);
lean_inc(v___x_956_);
v___x_960_ = l_Lean_Syntax_node1(v___y_943_, v___x_956_, v___x_959_);
v___x_961_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54));
v___x_962_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55));
v___x_963_ = l_Lean_Name_mkStr4(v___y_941_, v___x_951_, v___x_961_, v___x_962_);
v___x_964_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57);
v___x_965_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59));
v___x_966_ = l_Lean_addMacroScope(v_a_950_, v___x_965_, v___y_949_);
lean_inc(v___y_939_);
v___x_967_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_967_, 0, v___y_943_);
lean_ctor_set(v___x_967_, 1, v___x_964_);
lean_ctor_set(v___x_967_, 2, v___x_966_);
lean_ctor_set(v___x_967_, 3, v___y_939_);
v___x_968_ = l_Lean_Syntax_node2(v___y_943_, v___x_963_, v___x_967_, v___x_959_);
lean_inc(v___x_954_);
v___x_969_ = l_Lean_Syntax_node2(v___y_943_, v___x_954_, v___x_960_, v___x_968_);
v___x_970_ = lean_mk_empty_array_with_capacity(v___x_687_);
v___x_971_ = lean_array_push(v___x_970_, v___x_969_);
v___x_972_ = l_Lake_DSL_expandAttrs(v___y_946_);
v___x_973_ = l_Array_append___redArg(v___x_971_, v___x_972_);
lean_dec_ref(v___x_972_);
v___x_974_ = l_Lake_DSL_packageDeclName;
v___x_975_ = l_Lean_mkIdentFrom(v___y_935_, v___x_974_, v___y_948_);
lean_dec(v___y_935_);
v___x_976_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_947_, v___y_942_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
v___x_978_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_947_);
if (lean_obj_tag(v___x_978_) == 0)
{
if (lean_obj_tag(v___y_944_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; lean_object* v_a_981_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_942_);
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref(v___x_980_);
v___y_828_ = v___x_951_;
v___y_829_ = v___x_954_;
v___y_830_ = v___y_934_;
v___y_831_ = v___x_975_;
v___y_832_ = v___x_974_;
v___y_833_ = v___y_936_;
v___y_834_ = v___y_937_;
v___y_835_ = v___y_938_;
v___y_836_ = v___y_939_;
v___y_837_ = v___y_941_;
v___y_838_ = v___y_940_;
v___y_839_ = v___y_942_;
v___y_840_ = v___x_973_;
v___y_841_ = v___x_957_;
v___y_842_ = v_a_979_;
v___y_843_ = v___y_944_;
v___y_844_ = v___x_958_;
v___y_845_ = v___x_956_;
v___y_846_ = v_a_977_;
v___y_847_ = v___y_945_;
v___y_848_ = v___x_952_;
v___y_849_ = v___y_947_;
v___y_850_ = v___y_948_;
v_a_851_ = v_a_981_;
goto v___jp_827_;
}
else
{
lean_object* v_a_982_; lean_object* v_val_983_; 
v_a_982_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_978_, 1);
v_val_983_ = lean_ctor_get(v___y_944_, 0);
lean_inc(v_val_983_);
v___y_828_ = v___x_951_;
v___y_829_ = v___x_954_;
v___y_830_ = v___y_934_;
v___y_831_ = v___x_975_;
v___y_832_ = v___x_974_;
v___y_833_ = v___y_936_;
v___y_834_ = v___y_937_;
v___y_835_ = v___y_938_;
v___y_836_ = v___y_939_;
v___y_837_ = v___y_941_;
v___y_838_ = v___y_940_;
v___y_839_ = v___y_942_;
v___y_840_ = v___x_973_;
v___y_841_ = v___x_957_;
v___y_842_ = v_a_982_;
v___y_843_ = v___y_944_;
v___y_844_ = v___x_958_;
v___y_845_ = v___x_956_;
v___y_846_ = v_a_977_;
v___y_847_ = v___y_945_;
v___y_848_ = v___x_952_;
v___y_849_ = v___y_947_;
v___y_850_ = v___y_948_;
v_a_851_ = v_val_983_;
goto v___jp_827_;
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_a_977_);
lean_dec(v___x_975_);
lean_dec_ref(v___x_973_);
lean_dec(v___x_956_);
lean_dec(v___x_954_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_945_);
lean_dec(v___y_944_);
lean_dec(v___y_940_);
lean_dec(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v___y_934_);
lean_dec(v_stx_607_);
v_a_984_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_978_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_978_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec(v___x_975_);
lean_dec_ref(v___x_973_);
lean_dec(v___x_956_);
lean_dec(v___x_954_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_945_);
lean_dec(v___y_944_);
lean_dec(v___y_940_);
lean_dec(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v___y_934_);
lean_dec(v_stx_607_);
v_a_992_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_976_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_976_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
v___jp_1000_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1014_ = l_Nat_reprFast(v___y_1006_);
v___x_1015_ = lean_box(2);
v___x_1016_ = l_Lean_Syntax_mkNumLit(v___x_1014_, v___x_1015_);
v___x_1017_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1018_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62));
v___x_1019_ = lean_mk_empty_array_with_capacity(v___x_689_);
lean_inc(v___y_1013_);
lean_inc_ref(v___x_1019_);
v___x_1020_ = lean_array_push(v___x_1019_, v___y_1013_);
v___x_1021_ = lean_array_push(v___x_1020_, v___x_1016_);
v___x_1022_ = l_Lean_Syntax_mkCApp(v___x_1018_, v___x_1021_);
v___x_1023_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64));
lean_inc(v___x_1022_);
v___x_1024_ = lean_array_push(v___x_1019_, v___x_1022_);
lean_inc(v___y_1007_);
v___x_1025_ = lean_array_push(v___x_1024_, v___y_1007_);
v___x_1026_ = l_Lean_Syntax_mkCApp(v___x_1023_, v___x_1025_);
lean_inc(v___y_1001_);
lean_inc(v___y_1004_);
v___x_1027_ = l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v___x_1023_, v___y_1004_, v___x_1026_, v___y_1001_, v___y_1010_, v___y_1008_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc_n(v_a_1028_, 2);
lean_dec_ref_known(v___x_1027_, 1);
v___x_1029_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_1029_, 0, v_a_1028_);
v___x_1030_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v___y_1001_, v_a_1028_, v___x_1029_, v___y_1010_, v___y_1008_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v___x_1031_; 
lean_dec_ref_known(v___x_1030_, 1);
v___x_1031_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_1010_, v___y_1008_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1010_);
if (lean_obj_tag(v___x_1033_) == 0)
{
if (lean_obj_tag(v___y_1009_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1035_; lean_object* v_a_1036_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
v___x_1035_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1008_);
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref(v___x_1035_);
v___y_934_ = v___x_1015_;
v___y_935_ = v___y_1002_;
v___y_936_ = v___x_1022_;
v___y_937_ = v___y_1003_;
v___y_938_ = v___y_1004_;
v___y_939_ = v___y_1005_;
v___y_940_ = v___y_1007_;
v___y_941_ = v___x_1017_;
v___y_942_ = v___y_1008_;
v___y_943_ = v_a_1032_;
v___y_944_ = v___y_1009_;
v___y_945_ = v___y_1013_;
v___y_946_ = v___y_1011_;
v___y_947_ = v___y_1010_;
v___y_948_ = v___y_1012_;
v___y_949_ = v_a_1034_;
v_a_950_ = v_a_1036_;
goto v___jp_933_;
}
else
{
lean_object* v_a_1037_; lean_object* v_val_1038_; 
v_a_1037_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1033_, 1);
v_val_1038_ = lean_ctor_get(v___y_1009_, 0);
lean_inc(v_val_1038_);
v___y_934_ = v___x_1015_;
v___y_935_ = v___y_1002_;
v___y_936_ = v___x_1022_;
v___y_937_ = v___y_1003_;
v___y_938_ = v___y_1004_;
v___y_939_ = v___y_1005_;
v___y_940_ = v___y_1007_;
v___y_941_ = v___x_1017_;
v___y_942_ = v___y_1008_;
v___y_943_ = v_a_1032_;
v___y_944_ = v___y_1009_;
v___y_945_ = v___y_1013_;
v___y_946_ = v___y_1011_;
v___y_947_ = v___y_1010_;
v___y_948_ = v___y_1012_;
v___y_949_ = v_a_1037_;
v_a_950_ = v_val_1038_;
goto v___jp_933_;
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v_a_1032_);
lean_dec(v___x_1022_);
lean_dec(v___y_1013_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec(v___y_1007_);
lean_dec(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec(v_stx_607_);
v_a_1039_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1033_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1033_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v___x_1022_);
lean_dec(v___y_1013_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec(v___y_1007_);
lean_dec(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec(v_stx_607_);
v_a_1047_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1031_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1031_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_dec(v___x_1022_);
lean_dec(v___y_1013_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec(v___y_1007_);
lean_dec(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec(v_stx_607_);
return v___x_1030_;
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v___x_1022_);
lean_dec(v___y_1013_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec(v___y_1007_);
lean_dec(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec(v_stx_607_);
v_a_1055_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1027_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1027_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
v___jp_1063_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1075_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66);
v___x_1076_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67));
v___x_1077_ = l_Lean_addMacroScope(v_a_1074_, v___x_1076_, v___y_1068_);
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1079_, 0, v___y_1065_);
lean_ctor_set(v___x_1079_, 1, v___x_1075_);
lean_ctor_set(v___x_1079_, 2, v___x_1077_);
lean_ctor_set(v___x_1079_, 3, v___x_1078_);
v___x_1080_ = l_Lake_DSL_mkConfigDeclIdent(v___y_1069_, v___y_1071_, v___y_1073_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v_env_1085_; lean_object* v___x_1086_; lean_object* v_asyncMode_1087_; lean_object* v___x_1088_; lean_object* v_snd_1089_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc_n(v_a_1081_, 2);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = l_Lean_TSyntax_getId(v_a_1081_);
v___x_1083_ = l_Lake_Name_quoteFrom(v_a_1081_, v___x_1082_, v___y_1072_);
v___x_1084_ = lean_st_ref_get(v___y_1073_);
v_env_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc_ref(v_env_1085_);
lean_dec(v___x_1084_);
v___x_1086_ = l_Lake_nameExt;
v_asyncMode_1087_ = lean_ctor_get(v___x_1086_, 2);
v___x_1088_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_685_, v___x_1086_, v_env_1085_, v_asyncMode_1087_, v___x_684_, v___y_1072_);
v_snd_1089_ = lean_ctor_get(v___x_1088_, 1);
if (lean_obj_tag(v_snd_1089_) == 0)
{
lean_object* v_fst_1090_; 
v_fst_1090_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_fst_1090_);
lean_dec(v___x_1088_);
lean_inc(v___x_1083_);
v___y_1001_ = v___y_1066_;
v___y_1002_ = v_a_1081_;
v___y_1003_ = v___y_1067_;
v___y_1004_ = v___x_1079_;
v___y_1005_ = v___x_1078_;
v___y_1006_ = v_fst_1090_;
v___y_1007_ = v___x_1083_;
v___y_1008_ = v___y_1073_;
v___y_1009_ = v___y_1064_;
v___y_1010_ = v___y_1071_;
v___y_1011_ = v___y_1070_;
v___y_1012_ = v___y_1072_;
v___y_1013_ = v___x_1083_;
goto v___jp_1000_;
}
else
{
lean_object* v_fst_1091_; lean_object* v___x_1092_; 
lean_inc(v_snd_1089_);
v_fst_1091_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_fst_1091_);
lean_dec(v___x_1088_);
lean_inc(v_a_1081_);
v___x_1092_ = l_Lake_Name_quoteFrom(v_a_1081_, v_snd_1089_, v___y_1072_);
v___y_1001_ = v___y_1066_;
v___y_1002_ = v_a_1081_;
v___y_1003_ = v___y_1067_;
v___y_1004_ = v___x_1079_;
v___y_1005_ = v___x_1078_;
v___y_1006_ = v_fst_1091_;
v___y_1007_ = v___x_1083_;
v___y_1008_ = v___y_1073_;
v___y_1009_ = v___y_1064_;
v___y_1010_ = v___y_1071_;
v___y_1011_ = v___y_1070_;
v___y_1012_ = v___y_1072_;
v___y_1013_ = v___x_1092_;
goto v___jp_1000_;
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec_ref_known(v___x_1079_, 4);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec(v___y_1064_);
lean_dec(v_stx_607_);
v_a_1093_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1080_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1080_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
v___jp_1102_:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Elab_Command_getRef___redArg(v___y_1103_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v_fileName_1111_; lean_object* v_fileMap_1112_; lean_object* v_currRecDepth_1113_; lean_object* v_cmdPos_1114_; lean_object* v_macroStack_1115_; lean_object* v_quotContext_x3f_1116_; lean_object* v_currMacroScope_1117_; lean_object* v_snap_x3f_1118_; lean_object* v_cancelTk_x3f_1119_; uint8_t v_suppressElabErrors_1120_; uint8_t v_checkDeprecated_1121_; lean_object* v_ref_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v_fileName_1111_ = lean_ctor_get(v___y_1103_, 0);
v_fileMap_1112_ = lean_ctor_get(v___y_1103_, 1);
v_currRecDepth_1113_ = lean_ctor_get(v___y_1103_, 2);
v_cmdPos_1114_ = lean_ctor_get(v___y_1103_, 3);
v_macroStack_1115_ = lean_ctor_get(v___y_1103_, 4);
v_quotContext_x3f_1116_ = lean_ctor_get(v___y_1103_, 5);
v_currMacroScope_1117_ = lean_ctor_get(v___y_1103_, 6);
v_snap_x3f_1118_ = lean_ctor_get(v___y_1103_, 8);
v_cancelTk_x3f_1119_ = lean_ctor_get(v___y_1103_, 9);
v_suppressElabErrors_1120_ = lean_ctor_get_uint8(v___y_1103_, sizeof(void*)*10);
v_checkDeprecated_1121_ = lean_ctor_get_uint8(v___y_1103_, sizeof(void*)*10 + 1);
v_ref_1122_ = l_Lean_replaceRef(v_kw_1101_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec(v_kw_1101_);
lean_inc(v_cancelTk_x3f_1119_);
lean_inc(v_snap_x3f_1118_);
lean_inc(v_currMacroScope_1117_);
lean_inc(v_quotContext_x3f_1116_);
lean_inc(v_macroStack_1115_);
lean_inc(v_cmdPos_1114_);
lean_inc(v_currRecDepth_1113_);
lean_inc_ref(v_fileMap_1112_);
lean_inc_ref(v_fileName_1111_);
v___x_1123_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1123_, 0, v_fileName_1111_);
lean_ctor_set(v___x_1123_, 1, v_fileMap_1112_);
lean_ctor_set(v___x_1123_, 2, v_currRecDepth_1113_);
lean_ctor_set(v___x_1123_, 3, v_cmdPos_1114_);
lean_ctor_set(v___x_1123_, 4, v_macroStack_1115_);
lean_ctor_set(v___x_1123_, 5, v_quotContext_x3f_1116_);
lean_ctor_set(v___x_1123_, 6, v_currMacroScope_1117_);
lean_ctor_set(v___x_1123_, 7, v_ref_1122_);
lean_ctor_set(v___x_1123_, 8, v_snap_x3f_1118_);
lean_ctor_set(v___x_1123_, 9, v_cancelTk_x3f_1119_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*10, v_suppressElabErrors_1120_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*10 + 1, v_checkDeprecated_1121_);
v___x_1124_ = l_Lean_Elab_Command_getRef___redArg(v___x_1123_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref_known(v___x_1124_, 1);
v___x_1126_ = 0;
v___x_1127_ = l_Lean_SourceInfo_fromRef(v_a_1125_, v___x_1126_);
lean_dec(v_a_1125_);
v___x_1128_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1123_);
if (lean_obj_tag(v___x_1128_) == 0)
{
if (lean_obj_tag(v_quotContext_x3f_1116_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; lean_object* v_a_1131_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1107_);
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref(v___x_1130_);
v___y_1064_ = v_quotContext_x3f_1116_;
v___y_1065_ = v___x_1127_;
v___y_1066_ = v___y_1104_;
v___y_1067_ = v___y_1108_;
v___y_1068_ = v_a_1129_;
v___y_1069_ = v___y_1105_;
v___y_1070_ = v___y_1106_;
v___y_1071_ = v___x_1123_;
v___y_1072_ = v___x_1126_;
v___y_1073_ = v___y_1107_;
v_a_1074_ = v_a_1131_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1132_; lean_object* v_val_1133_; 
v_a_1132_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1128_, 1);
v_val_1133_ = lean_ctor_get(v_quotContext_x3f_1116_, 0);
lean_inc(v_val_1133_);
lean_inc_ref(v_quotContext_x3f_1116_);
v___y_1064_ = v_quotContext_x3f_1116_;
v___y_1065_ = v___x_1127_;
v___y_1066_ = v___y_1104_;
v___y_1067_ = v___y_1108_;
v___y_1068_ = v_a_1132_;
v___y_1069_ = v___y_1105_;
v___y_1070_ = v___y_1106_;
v___y_1071_ = v___x_1123_;
v___y_1072_ = v___x_1126_;
v___y_1073_ = v___y_1107_;
v_a_1074_ = v_val_1133_;
goto v___jp_1063_;
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v___x_1127_);
lean_dec_ref_known(v___x_1123_, 10);
lean_dec(v___y_1108_);
lean_dec(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec(v_stx_607_);
v_a_1134_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1128_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1128_);
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
lean_dec_ref_known(v___x_1123_, 10);
lean_dec(v___y_1108_);
lean_dec(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec(v_stx_607_);
v_a_1142_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1124_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1124_);
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
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v___y_1108_);
lean_dec(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec(v_kw_1101_);
lean_dec(v_stx_607_);
v_a_1150_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1109_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1109_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
v___jp_1158_:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_Syntax_getOptional_x3f(v___x_686_);
lean_dec(v___x_686_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_box(0);
v___y_1103_ = v___y_1159_;
v___y_1104_ = v___y_1160_;
v___y_1105_ = v___y_1161_;
v___y_1106_ = v___y_1163_;
v___y_1107_ = v___y_1162_;
v___y_1108_ = v___x_1165_;
goto v___jp_1102_;
}
else
{
lean_object* v_val_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_val_1166_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1164_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_val_1166_);
lean_dec(v___x_1164_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_val_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
v___y_1103_ = v___y_1159_;
v___y_1104_ = v___y_1160_;
v___y_1105_ = v___y_1161_;
v___y_1106_ = v___y_1163_;
v___y_1107_ = v___y_1162_;
v___y_1108_ = v___x_1171_;
goto v___jp_1102_;
}
}
}
}
v___jp_1174_:
{
lean_object* v___x_1178_; lean_object* v_cfg_1179_; lean_object* v___x_1180_; 
v___x_1178_ = lean_unsigned_to_nat(4u);
v_cfg_1179_ = l_Lean_Syntax_getArg(v_stx_607_, v___x_1178_);
v___x_1180_ = l_Lean_Syntax_getOptional_x3f(v___x_688_);
lean_dec(v___x_688_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_box(0);
v___y_1159_ = v___y_1176_;
v___y_1160_ = v_cfg_1179_;
v___y_1161_ = v_nameStx_x3f_1175_;
v___y_1162_ = v___y_1177_;
v___y_1163_ = v___x_1181_;
goto v___jp_1158_;
}
else
{
lean_object* v_val_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
v_val_1182_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1180_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_val_1182_);
lean_dec(v___x_1180_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_val_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
v___y_1159_ = v___y_1176_;
v___y_1160_ = v_cfg_1179_;
v___y_1161_ = v_nameStx_x3f_1175_;
v___y_1162_ = v___y_1177_;
v___y_1163_ = v___x_1187_;
goto v___jp_1158_;
}
}
}
}
}
v___jp_611_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
lean_inc_ref(v___y_628_);
lean_inc_n(v___y_626_, 5);
lean_inc_n(v___y_618_, 28);
v___x_636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_636_, 0, v___y_618_);
lean_ctor_set(v___x_636_, 1, v___y_626_);
lean_ctor_set(v___x_636_, 2, v___y_628_);
lean_inc_ref(v___y_616_);
v___x_637_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_637_, 0, v___y_618_);
lean_ctor_set(v___x_637_, 1, v___y_616_);
lean_inc_ref_n(v___x_636_, 13);
v___x_638_ = l_Lean_Syntax_node1(v___y_618_, v___y_629_, v___x_636_);
v___x_639_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0));
lean_inc_ref(v___y_622_);
v___x_640_ = l_Lean_Name_mkStr2(v___y_622_, v___x_639_);
v___x_641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_641_, 0, v___y_618_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
v___x_642_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2));
v___x_643_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3));
v___x_644_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_644_, 0, v___y_618_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = l_Lean_Syntax_node1(v___y_618_, v___x_642_, v___x_644_);
v___x_646_ = l_Lean_Syntax_node1(v___y_618_, v___y_626_, v___x_645_);
v___x_647_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4));
v___x_648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_648_, 0, v___y_618_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5));
v___x_650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_650_, 0, v___y_618_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
lean_inc_ref(v___y_612_);
v___x_651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_651_, 0, v___y_618_);
lean_ctor_set(v___x_651_, 1, v___y_612_);
v___x_652_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6));
v___x_653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_653_, 0, v___y_618_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_Syntax_node1(v___y_618_, v___x_642_, v___x_653_);
v___x_655_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7));
v___x_656_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_656_, 0, v___y_618_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
lean_inc_ref(v___x_651_);
v___x_657_ = l_Lean_Syntax_node5(v___y_618_, v___y_626_, v___x_648_, v___x_650_, v___x_651_, v___x_654_, v___x_656_);
v___x_658_ = l_Lean_Syntax_node5(v___y_618_, v___x_640_, v___x_641_, v___x_636_, v___x_646_, v___x_636_, v___x_657_);
v___x_659_ = l_Lean_Syntax_node2(v___y_618_, v___y_613_, v___x_638_, v___x_658_);
v___x_660_ = l_Lean_Syntax_node1(v___y_618_, v___y_626_, v___x_659_);
lean_inc_ref(v___y_630_);
v___x_661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_661_, 0, v___y_618_);
lean_ctor_set(v___x_661_, 1, v___y_630_);
v___x_662_ = l_Lean_Syntax_node3(v___y_618_, v___y_627_, v___x_637_, v___x_660_, v___x_661_);
v___x_663_ = l_Lean_Syntax_node1(v___y_618_, v___y_626_, v___x_662_);
v___x_664_ = l_Lean_Syntax_node7(v___y_618_, v___y_617_, v___x_636_, v___x_663_, v___x_636_, v___x_636_, v___x_636_, v___x_636_, v___x_636_);
v___x_665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_665_, 0, v___y_618_);
lean_ctor_set(v___x_665_, 1, v___y_619_);
v___x_666_ = lean_array_push(v___y_615_, v___y_634_);
v___x_667_ = lean_array_push(v___x_666_, v___y_632_);
v___x_668_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_668_, 0, v___y_614_);
lean_ctor_set(v___x_668_, 1, v___y_633_);
lean_ctor_set(v___x_668_, 2, v___x_667_);
v___x_669_ = l_Lean_Syntax_node2(v___y_618_, v___y_621_, v___x_636_, v___x_636_);
v___x_670_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9));
v___x_671_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10));
v___x_672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_672_, 0, v___y_618_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = l_Lean_Syntax_node1(v___y_618_, v___x_670_, v___x_672_);
v___x_674_ = l_Lean_Syntax_node2(v___y_618_, v___y_635_, v___x_636_, v___x_636_);
v___x_675_ = l_Lean_Syntax_node4(v___y_618_, v___y_620_, v___x_651_, v___x_673_, v___x_674_, v___x_636_);
v___x_676_ = l_Lean_Syntax_node4(v___y_618_, v___y_624_, v___x_665_, v___x_668_, v___x_669_, v___x_675_);
v___x_677_ = l_Lean_Syntax_node2(v___y_618_, v___y_623_, v___x_664_, v___x_676_);
v___x_678_ = l_Lean_Elab_Command_elabCommand(v___x_677_, v___y_631_, v___y_625_);
lean_dec_ref(v___y_631_);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed(lean_object* v_stx_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(v_stx_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(lean_object* v_00_u03b1_1204_, lean_object* v_ref_1205_, lean_object* v_msg_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_1205_, v_msg_1206_, v___y_1207_, v___y_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___boxed(lean_object* v_00_u03b1_1211_, lean_object* v_ref_1212_, lean_object* v_msg_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(v_00_u03b1_1211_, v_ref_1212_, v_msg_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v_ref_1212_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(lean_object* v_msgData_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msgData_1218_, v___y_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(v_msgData_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(lean_object* v_00_u03b1_1228_, lean_object* v_msg_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_1229_, v___y_1230_, v___y_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1234_, lean_object* v_msg_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(v_00_u03b1_1234_, v_msg_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(lean_object* v_msgData_1240_, lean_object* v_macroStack_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_1240_, v_macroStack_1241_, v___y_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1246_, lean_object* v_macroStack_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(v_msgData_1246_, v_macroStack_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1(){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1280_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1281_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12));
v___x_1282_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10));
v___x_1283_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed), 4, 0);
v___x_1284_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1280_, v___x_1281_, v___x_1282_, v___x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___boxed(lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
return v_res_1286_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3));
v___x_1295_ = l_String_toRawSubstring_x27(v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6));
v___x_1300_ = l_String_toRawSubstring_x27(v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12));
v___x_1313_ = l_String_toRawSubstring_x27(v___x_1312_);
return v___x_1313_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15));
v___x_1318_ = l_String_toRawSubstring_x27(v___x_1317_);
return v___x_1318_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21));
v___x_1326_ = l_String_toRawSubstring_x27(v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(lean_object* v_stx_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___x_1377_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; uint8_t v___x_1397_; 
v___x_1377_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1));
lean_inc(v_stx_1351_);
v___x_1397_ = l_Lean_Syntax_isOfKind(v_stx_1351_, v___x_1377_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1399_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1351_, v___x_1398_, v_a_1352_, v_a_1353_);
lean_dec(v_stx_1351_);
return v___x_1399_;
}
else
{
lean_object* v___x_1400_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; uint8_t v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v_wds_x3f_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v_wds_x3f_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v_pkg_x3f_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v_attrs_x3f_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v_doc_x3f_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1784_ = l_Lean_Syntax_getArg(v_stx_1351_, v___x_1400_);
v___x_1785_ = l_Lean_Syntax_isNone(v___x_1784_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1784_);
v___x_1787_ = l_Lean_Syntax_matchesNull(v___x_1784_, v___x_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_dec(v___x_1784_);
v___x_1788_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1789_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1351_, v___x_1788_, v_a_1352_, v_a_1353_);
lean_dec(v_stx_1351_);
return v___x_1789_;
}
else
{
lean_object* v_doc_x3f_1790_; lean_object* v___x_1791_; 
v_doc_x3f_1790_ = l_Lean_Syntax_getArg(v___x_1784_, v___x_1400_);
lean_dec(v___x_1784_);
v___x_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1791_, 0, v_doc_x3f_1790_);
v_doc_x3f_1772_ = v___x_1791_;
v___y_1773_ = v_a_1352_;
v___y_1774_ = v_a_1353_;
goto v___jp_1771_;
}
}
else
{
lean_object* v___x_1792_; 
lean_dec(v___x_1784_);
v___x_1792_ = lean_box(0);
v_doc_x3f_1772_ = v___x_1792_;
v___y_1773_ = v_a_1352_;
v___y_1774_ = v_a_1353_;
goto v___jp_1771_;
}
v___jp_1401_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_inc_ref_n(v___y_1415_, 2);
v___x_1423_ = l_Array_append___redArg(v___y_1415_, v___y_1422_);
lean_dec_ref(v___y_1422_);
lean_inc_n(v___y_1406_, 8);
lean_inc_n(v___y_1405_, 41);
v___x_1424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1424_, 0, v___y_1405_);
lean_ctor_set(v___x_1424_, 1, v___y_1406_);
lean_ctor_set(v___x_1424_, 2, v___x_1423_);
v___x_1425_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16));
lean_inc_ref_n(v___y_1404_, 9);
lean_inc_ref_n(v___y_1412_, 13);
lean_inc_ref_n(v___y_1421_, 13);
v___x_1426_ = l_Lean_Name_mkStr4(v___y_1421_, v___y_1412_, v___y_1404_, v___x_1425_);
v___x_1427_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17));
v___x_1428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___y_1405_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40));
v___x_1430_ = l_Lean_Syntax_SepArray_ofElems(v___x_1429_, v___y_1410_);
lean_dec_ref(v___y_1410_);
v___x_1431_ = l_Array_append___redArg(v___y_1415_, v___x_1430_);
lean_dec_ref(v___x_1430_);
v___x_1432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1432_, 0, v___y_1405_);
lean_ctor_set(v___x_1432_, 1, v___y_1406_);
lean_ctor_set(v___x_1432_, 2, v___x_1431_);
v___x_1433_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18));
v___x_1434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___y_1405_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = l_Lean_Syntax_node3(v___y_1405_, v___x_1426_, v___x_1428_, v___x_1432_, v___x_1434_);
v___x_1436_ = l_Lean_Syntax_node1(v___y_1405_, v___y_1406_, v___x_1435_);
lean_inc_n(v___y_1417_, 21);
v___x_1437_ = l_Lean_Syntax_node7(v___y_1405_, v___y_1408_, v___x_1424_, v___x_1436_, v___y_1417_, v___y_1417_, v___y_1417_, v___y_1417_, v___y_1417_);
v___x_1438_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5));
lean_inc_ref_n(v___y_1420_, 3);
v___x_1439_ = l_Lean_Name_mkStr4(v___y_1421_, v___y_1412_, v___y_1420_, v___x_1438_);
v___x_1440_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6));
v___x_1441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___y_1405_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_1443_ = l_Lean_Name_mkStr4(v___y_1421_, v___y_1412_, v___y_1420_, v___x_1442_);
v___x_1444_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4);
v___x_1445_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5));
lean_inc_n(v___y_1416_, 3);
lean_inc_n(v___y_1418_, 3);
v___x_1446_ = l_Lean_addMacroScope(v___y_1418_, v___x_1445_, v___y_1416_);
lean_inc_n(v___y_1403_, 4);
v___x_1447_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1447_, 0, v___y_1405_);
lean_ctor_set(v___x_1447_, 1, v___x_1444_);
lean_ctor_set(v___x_1447_, 2, v___x_1446_);
lean_ctor_set(v___x_1447_, 3, v___y_1403_);
v___x_1448_ = l_Lean_Syntax_node2(v___y_1405_, v___x_1443_, v___x_1447_, v___y_1417_);
v___x_1449_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_1450_ = l_Lean_Name_mkStr4(v___y_1421_, v___y_1412_, v___y_1420_, v___x_1449_);
v___x_1451_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_1452_ = l_Lean_Name_mkStr4(v___y_1421_, v___y_1412_, v___y_1404_, v___x_1451_);
v___x_1453_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_1454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___y_1405_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
v___x_1455_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7);
v___x_1456_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8));
v___x_1457_ = l_Lean_addMacroScope(v___y_1418_, v___x_1456_, v___y_1416_);
v___x_1458_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10));
v___x_1459_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11));
v___x_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v___y_1403_);
v___x_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1458_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1462_, 0, v___y_1405_);
lean_ctor_set(v___x_1462_, 1, v___x_1455_);
lean_ctor_set(v___x_1462_, 2, v___x_1457_);
lean_ctor_set(v___x_1462_, 3, v___x_1461_);
v___x_1463_ = l_Lean_Syntax_node2(v___y_1405_, v___x_1452_, v___x_1454_, v___x_1462_);
v___x_1464_ = l_Lean_Syntax_node1(v___y_1405_, v___y_1406_, v___x_1463_);
v___x_1465_ = l_Lean_Syntax_node2(v___y_1405_, v___x_1450_, v___y_1417_, v___x_1464_);
v___x_1466_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39));
v___x_1467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___y_1405_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31));
v___x_1469_ = l_Lean_Name_mkStr4(v___y_1421_, v___y_1412_, v___y_1404_, v___x_1468_);
v___x_1470_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32));
v___x_1471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___y_1405_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31));
v___x_1473_ = l_Lean_Name_mkStr4(v___y_1421_, v___y_1412_, v___y_1404_, v___x_1472_);
v___x_1474_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33));
v___x_1475_ = l_Lean_Name_mkStr4(v___y_1421_, v___y_1412_, v___y_1404_, v___x_1474_);
v___x_1476_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34));
v___x_1477_ = l_Lean_Name_mkStr4(v___y_1421_, v___y_1412_, v___y_1404_, v___x_1476_);
v___x_1478_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13);
v___x_1479_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14));
v___x_1480_ = l_Lean_addMacroScope(v___y_1418_, v___x_1479_, v___y_1416_);
v___x_1481_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1481_, 0, v___y_1405_);
lean_ctor_set(v___x_1481_, 1, v___x_1478_);
lean_ctor_set(v___x_1481_, 2, v___x_1480_);
lean_ctor_set(v___x_1481_, 3, v___y_1403_);
lean_inc(v___x_1477_);
v___x_1482_ = l_Lean_Syntax_node2(v___y_1405_, v___x_1477_, v___x_1481_, v___y_1417_);
v___x_1483_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38));
v___x_1484_ = l_Lean_Name_mkStr4(v___y_1421_, v___y_1412_, v___y_1404_, v___x_1483_);
v___x_1485_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9));
v___x_1486_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10));
v___x_1487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___y_1405_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Lean_Syntax_node1(v___y_1405_, v___x_1485_, v___x_1487_);
lean_inc_ref_n(v___x_1467_, 2);
lean_inc(v___x_1484_);
v___x_1489_ = l_Lean_Syntax_node3(v___y_1405_, v___x_1484_, v___x_1467_, v___y_1417_, v___x_1488_);
v___x_1490_ = l_Lean_Syntax_node3(v___y_1405_, v___y_1406_, v___y_1417_, v___y_1417_, v___x_1489_);
lean_inc(v___x_1475_);
v___x_1491_ = l_Lean_Syntax_node2(v___y_1405_, v___x_1475_, v___x_1482_, v___x_1490_);
v___x_1492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___y_1405_);
lean_ctor_set(v___x_1492_, 1, v___x_1429_);
v___x_1493_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16);
v___x_1494_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17));
v___x_1495_ = l_Lean_addMacroScope(v___y_1418_, v___x_1494_, v___y_1416_);
v___x_1496_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1405_);
lean_ctor_set(v___x_1496_, 1, v___x_1493_);
lean_ctor_set(v___x_1496_, 2, v___x_1495_);
lean_ctor_set(v___x_1496_, 3, v___y_1403_);
v___x_1497_ = l_Lean_Syntax_node2(v___y_1405_, v___x_1477_, v___x_1496_, v___y_1417_);
v___x_1498_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18));
v___x_1499_ = l_Lean_Name_mkStr4(v___y_1421_, v___y_1412_, v___y_1404_, v___x_1498_);
v___x_1500_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___y_1405_);
lean_ctor_set(v___x_1500_, 1, v___x_1498_);
v___x_1501_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19));
v___x_1502_ = l_Lean_Name_mkStr4(v___y_1421_, v___y_1412_, v___y_1404_, v___x_1501_);
v___x_1503_ = l_Lean_Syntax_node1(v___y_1405_, v___y_1406_, v___y_1407_);
v___x_1504_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20));
v___x_1505_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___y_1405_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = l_Lean_Syntax_node4(v___y_1405_, v___x_1502_, v___x_1503_, v___y_1417_, v___x_1505_, v___y_1419_);
v___x_1507_ = l_Lean_Syntax_node2(v___y_1405_, v___x_1499_, v___x_1500_, v___x_1506_);
v___x_1508_ = l_Lean_Syntax_node3(v___y_1405_, v___x_1484_, v___x_1467_, v___y_1417_, v___x_1507_);
v___x_1509_ = l_Lean_Syntax_node3(v___y_1405_, v___y_1406_, v___y_1417_, v___y_1417_, v___x_1508_);
v___x_1510_ = l_Lean_Syntax_node2(v___y_1405_, v___x_1475_, v___x_1497_, v___x_1509_);
v___x_1511_ = l_Lean_Syntax_node3(v___y_1405_, v___y_1406_, v___x_1491_, v___x_1492_, v___x_1510_);
v___x_1512_ = l_Lean_Syntax_node1(v___y_1405_, v___x_1473_, v___x_1511_);
v___x_1513_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50));
v___x_1514_ = l_Lean_Name_mkStr4(v___y_1421_, v___y_1412_, v___y_1404_, v___x_1513_);
v___x_1515_ = l_Lean_Syntax_node1(v___y_1405_, v___x_1514_, v___y_1417_);
v___x_1516_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51));
v___x_1517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___y_1405_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
v___x_1518_ = l_Lean_Syntax_node6(v___y_1405_, v___x_1469_, v___x_1471_, v___y_1417_, v___x_1512_, v___x_1515_, v___y_1417_, v___x_1517_);
lean_inc(v___y_1402_);
v___x_1519_ = l_Lean_Syntax_node2(v___y_1405_, v___y_1402_, v___y_1417_, v___y_1417_);
if (lean_obj_tag(v___y_1413_) == 1)
{
lean_object* v_val_1520_; lean_object* v___x_1521_; 
v_val_1520_ = lean_ctor_get(v___y_1413_, 0);
lean_inc(v_val_1520_);
lean_dec_ref_known(v___y_1413_, 1);
v___x_1521_ = l_Array_mkArray1___redArg(v_val_1520_);
v___y_1355_ = v___x_1437_;
v___y_1356_ = v___x_1439_;
v___y_1357_ = v___y_1405_;
v___y_1358_ = v___x_1518_;
v___y_1359_ = v___y_1406_;
v___y_1360_ = v___x_1441_;
v___y_1361_ = v___x_1465_;
v___y_1362_ = v___x_1467_;
v___y_1363_ = v___x_1519_;
v___y_1364_ = v___y_1409_;
v___y_1365_ = v___y_1411_;
v___y_1366_ = v___x_1448_;
v___y_1367_ = v___y_1414_;
v___y_1368_ = v___y_1415_;
v___y_1369_ = v___y_1417_;
v___y_1370_ = v___x_1521_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1522_; 
lean_dec(v___y_1413_);
v___x_1522_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1355_ = v___x_1437_;
v___y_1356_ = v___x_1439_;
v___y_1357_ = v___y_1405_;
v___y_1358_ = v___x_1518_;
v___y_1359_ = v___y_1406_;
v___y_1360_ = v___x_1441_;
v___y_1361_ = v___x_1465_;
v___y_1362_ = v___x_1467_;
v___y_1363_ = v___x_1519_;
v___y_1364_ = v___y_1409_;
v___y_1365_ = v___y_1411_;
v___y_1366_ = v___x_1448_;
v___y_1367_ = v___y_1414_;
v___y_1368_ = v___y_1415_;
v___y_1369_ = v___y_1417_;
v___y_1370_ = v___x_1522_;
goto v___jp_1354_;
}
}
v___jp_1523_:
{
lean_object* v_methods_1539_; lean_object* v_quotContext_1540_; lean_object* v_currMacroScope_1541_; lean_object* v_currRecDepth_1542_; lean_object* v_maxRecDepth_1543_; lean_object* v_ref_1544_; lean_object* v_ref_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_methods_1539_ = lean_ctor_get(v___y_1537_, 0);
v_quotContext_1540_ = lean_ctor_get(v___y_1537_, 1);
v_currMacroScope_1541_ = lean_ctor_get(v___y_1537_, 2);
v_currRecDepth_1542_ = lean_ctor_get(v___y_1537_, 3);
v_maxRecDepth_1543_ = lean_ctor_get(v___y_1537_, 4);
v_ref_1544_ = lean_ctor_get(v___y_1537_, 5);
v_ref_1545_ = l_Lean_replaceRef(v___y_1534_, v_ref_1544_);
lean_dec(v___y_1534_);
lean_inc(v_ref_1545_);
lean_inc(v_maxRecDepth_1543_);
lean_inc(v_currRecDepth_1542_);
lean_inc(v_currMacroScope_1541_);
lean_inc(v_quotContext_1540_);
lean_inc(v_methods_1539_);
v___x_1546_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1546_, 0, v_methods_1539_);
lean_ctor_set(v___x_1546_, 1, v_quotContext_1540_);
lean_ctor_set(v___x_1546_, 2, v_currMacroScope_1541_);
lean_ctor_set(v___x_1546_, 3, v_currRecDepth_1542_);
lean_ctor_set(v___x_1546_, 4, v_maxRecDepth_1543_);
lean_ctor_set(v___x_1546_, 5, v_ref_1545_);
v___x_1547_ = l_Lake_DSL_expandOptSimpleBinder(v___y_1528_, v___x_1546_, v___y_1538_);
lean_dec_ref_known(v___x_1546_, 6);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v_a_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
v_a_1549_ = lean_ctor_get(v___x_1547_, 1);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1547_, 2);
v___x_1550_ = l_Lean_SourceInfo_fromRef(v_ref_1545_, v___y_1533_);
lean_dec(v_ref_1545_);
v___x_1551_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_1552_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52));
lean_inc_ref_n(v___y_1526_, 5);
lean_inc_ref_n(v___y_1535_, 5);
v___x_1553_ = l_Lean_Name_mkStr4(v___y_1535_, v___y_1526_, v___x_1551_, v___x_1552_);
v___x_1554_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53));
v___x_1555_ = l_Lean_Name_mkStr4(v___y_1535_, v___y_1526_, v___x_1551_, v___x_1554_);
v___x_1556_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_1557_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___x_1550_, 5);
v___x_1558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1550_);
lean_ctor_set(v___x_1558_, 1, v___x_1556_);
lean_ctor_set(v___x_1558_, 2, v___x_1557_);
lean_inc_ref_n(v___x_1558_, 2);
v___x_1559_ = l_Lean_Syntax_node1(v___x_1550_, v___x_1555_, v___x_1558_);
v___x_1560_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54));
v___x_1561_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55));
v___x_1562_ = l_Lean_Name_mkStr4(v___y_1535_, v___y_1526_, v___x_1560_, v___x_1561_);
v___x_1563_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22);
v___x_1564_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24));
lean_inc(v_currMacroScope_1541_);
lean_inc(v_quotContext_1540_);
v___x_1565_ = l_Lean_addMacroScope(v_quotContext_1540_, v___x_1564_, v_currMacroScope_1541_);
v___x_1566_ = lean_box(0);
v___x_1567_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1550_);
lean_ctor_set(v___x_1567_, 1, v___x_1563_);
lean_ctor_set(v___x_1567_, 2, v___x_1565_);
lean_ctor_set(v___x_1567_, 3, v___x_1566_);
v___x_1568_ = l_Lean_Syntax_node2(v___x_1550_, v___x_1562_, v___x_1567_, v___x_1558_);
v___x_1569_ = l_Lean_Syntax_node2(v___x_1550_, v___x_1553_, v___x_1559_, v___x_1568_);
v___x_1570_ = lean_mk_empty_array_with_capacity(v___y_1530_);
v___x_1571_ = lean_array_push(v___x_1570_, v___x_1569_);
v___x_1572_ = l_Lake_DSL_expandAttrs(v___y_1529_);
v___x_1573_ = l_Array_append___redArg(v___x_1571_, v___x_1572_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_1532_, 2);
v___x_1575_ = l_Lean_Name_mkStr4(v___y_1535_, v___y_1526_, v___y_1532_, v___x_1574_);
v___x_1576_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_1577_ = l_Lean_Name_mkStr4(v___y_1535_, v___y_1526_, v___y_1532_, v___x_1576_);
if (lean_obj_tag(v___y_1527_) == 1)
{
lean_object* v_val_1578_; lean_object* v___x_1579_; 
v_val_1578_ = lean_ctor_get(v___y_1527_, 0);
lean_inc(v_val_1578_);
lean_dec_ref_known(v___y_1527_, 1);
v___x_1579_ = l_Array_mkArray1___redArg(v_val_1578_);
lean_inc(v_quotContext_1540_);
lean_inc(v_currMacroScope_1541_);
v___y_1402_ = v___y_1524_;
v___y_1403_ = v___x_1566_;
v___y_1404_ = v___x_1551_;
v___y_1405_ = v___x_1550_;
v___y_1406_ = v___x_1556_;
v___y_1407_ = v_a_1548_;
v___y_1408_ = v___x_1577_;
v___y_1409_ = v___x_1575_;
v___y_1410_ = v___x_1573_;
v___y_1411_ = v___y_1525_;
v___y_1412_ = v___y_1526_;
v___y_1413_ = v_wds_x3f_1536_;
v___y_1414_ = v_a_1549_;
v___y_1415_ = v___x_1557_;
v___y_1416_ = v_currMacroScope_1541_;
v___y_1417_ = v___x_1558_;
v___y_1418_ = v_quotContext_1540_;
v___y_1419_ = v___y_1531_;
v___y_1420_ = v___y_1532_;
v___y_1421_ = v___y_1535_;
v___y_1422_ = v___x_1579_;
goto v___jp_1401_;
}
else
{
lean_object* v___x_1580_; 
lean_dec(v___y_1527_);
v___x_1580_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
lean_inc(v_quotContext_1540_);
lean_inc(v_currMacroScope_1541_);
v___y_1402_ = v___y_1524_;
v___y_1403_ = v___x_1566_;
v___y_1404_ = v___x_1551_;
v___y_1405_ = v___x_1550_;
v___y_1406_ = v___x_1556_;
v___y_1407_ = v_a_1548_;
v___y_1408_ = v___x_1577_;
v___y_1409_ = v___x_1575_;
v___y_1410_ = v___x_1573_;
v___y_1411_ = v___y_1525_;
v___y_1412_ = v___y_1526_;
v___y_1413_ = v_wds_x3f_1536_;
v___y_1414_ = v_a_1549_;
v___y_1415_ = v___x_1557_;
v___y_1416_ = v_currMacroScope_1541_;
v___y_1417_ = v___x_1558_;
v___y_1418_ = v_quotContext_1540_;
v___y_1419_ = v___y_1531_;
v___y_1420_ = v___y_1532_;
v___y_1421_ = v___y_1535_;
v___y_1422_ = v___x_1580_;
goto v___jp_1401_;
}
}
else
{
lean_object* v_a_1581_; lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_ref_1545_);
lean_dec(v_wds_x3f_1536_);
lean_dec(v___y_1531_);
lean_dec(v___y_1529_);
lean_dec(v___y_1527_);
v_a_1581_ = lean_ctor_get(v___x_1547_, 0);
v_a_1582_ = lean_ctor_get(v___x_1547_, 1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1547_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_inc(v_a_1581_);
lean_dec(v___x_1547_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1581_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
v___jp_1590_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_inc_ref_n(v___y_1593_, 2);
v___x_1605_ = l_Array_append___redArg(v___y_1593_, v___y_1604_);
lean_dec_ref(v___y_1604_);
lean_inc_n(v___y_1596_, 2);
lean_inc_n(v___y_1595_, 6);
v___x_1606_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1606_, 0, v___y_1595_);
lean_ctor_set(v___x_1606_, 1, v___y_1596_);
lean_ctor_set(v___x_1606_, 2, v___x_1605_);
v___x_1607_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_1608_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26));
lean_inc_ref_n(v___y_1600_, 2);
lean_inc_ref_n(v___y_1597_, 2);
v___x_1609_ = l_Lean_Name_mkStr4(v___y_1597_, v___y_1600_, v___x_1607_, v___x_1608_);
v___x_1610_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39));
v___x_1611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___y_1595_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
lean_inc_ref(v___y_1602_);
v___x_1612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___y_1595_);
lean_ctor_set(v___x_1612_, 1, v___y_1602_);
lean_inc(v___y_1603_);
v___x_1613_ = l_Lean_Syntax_node2(v___y_1595_, v___y_1603_, v___x_1612_, v___y_1599_);
v___x_1614_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27));
v___x_1615_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___x_1616_ = l_Lean_Name_mkStr4(v___y_1597_, v___y_1600_, v___x_1614_, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1617_, 0, v___y_1595_);
lean_ctor_set(v___x_1617_, 1, v___y_1596_);
lean_ctor_set(v___x_1617_, 2, v___y_1593_);
lean_inc_ref(v___x_1617_);
v___x_1618_ = l_Lean_Syntax_node2(v___y_1595_, v___x_1616_, v___x_1617_, v___x_1617_);
if (lean_obj_tag(v___y_1601_) == 1)
{
lean_object* v_val_1619_; lean_object* v___x_1620_; 
v_val_1619_ = lean_ctor_get(v___y_1601_, 0);
lean_inc(v_val_1619_);
lean_dec_ref_known(v___y_1601_, 1);
v___x_1620_ = l_Array_mkArray1___redArg(v_val_1619_);
v___y_1379_ = v___x_1611_;
v___y_1380_ = v___y_1598_;
v___y_1381_ = v___y_1591_;
v___y_1382_ = v___x_1618_;
v___y_1383_ = v___y_1592_;
v___y_1384_ = v___x_1609_;
v___y_1385_ = v___x_1613_;
v___y_1386_ = v___y_1593_;
v___y_1387_ = v___y_1594_;
v___y_1388_ = v___y_1596_;
v___y_1389_ = v___y_1595_;
v___y_1390_ = v___x_1606_;
v___y_1391_ = v___x_1620_;
goto v___jp_1378_;
}
else
{
lean_object* v___x_1621_; 
lean_dec(v___y_1601_);
v___x_1621_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1379_ = v___x_1611_;
v___y_1380_ = v___y_1598_;
v___y_1381_ = v___y_1591_;
v___y_1382_ = v___x_1618_;
v___y_1383_ = v___y_1592_;
v___y_1384_ = v___x_1609_;
v___y_1385_ = v___x_1613_;
v___y_1386_ = v___y_1593_;
v___y_1387_ = v___y_1594_;
v___y_1388_ = v___y_1596_;
v___y_1389_ = v___y_1595_;
v___y_1390_ = v___x_1606_;
v___y_1391_ = v___x_1621_;
goto v___jp_1378_;
}
}
v___jp_1622_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_inc_ref(v___y_1624_);
v___x_1637_ = l_Array_append___redArg(v___y_1624_, v___y_1636_);
lean_dec_ref(v___y_1636_);
lean_inc(v___y_1627_);
lean_inc(v___y_1626_);
v___x_1638_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1638_, 0, v___y_1626_);
lean_ctor_set(v___x_1638_, 1, v___y_1627_);
lean_ctor_set(v___x_1638_, 2, v___x_1637_);
v___x_1639_ = l_Lean_SourceInfo_fromRef(v___y_1634_, v___x_1397_);
lean_dec(v___y_1634_);
v___x_1640_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23));
v___x_1641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
if (lean_obj_tag(v___y_1629_) == 1)
{
lean_object* v_val_1642_; lean_object* v___x_1643_; 
v_val_1642_ = lean_ctor_get(v___y_1629_, 0);
lean_inc(v_val_1642_);
lean_dec_ref_known(v___y_1629_, 1);
v___x_1643_ = l_Array_mkArray1___redArg(v_val_1642_);
v___y_1591_ = v___x_1638_;
v___y_1592_ = v___y_1623_;
v___y_1593_ = v___y_1624_;
v___y_1594_ = v___y_1625_;
v___y_1595_ = v___y_1626_;
v___y_1596_ = v___y_1627_;
v___y_1597_ = v___y_1628_;
v___y_1598_ = v___x_1641_;
v___y_1599_ = v___y_1630_;
v___y_1600_ = v___y_1631_;
v___y_1601_ = v___y_1632_;
v___y_1602_ = v___y_1633_;
v___y_1603_ = v___y_1635_;
v___y_1604_ = v___x_1643_;
goto v___jp_1590_;
}
else
{
lean_object* v___x_1644_; 
lean_dec(v___y_1629_);
v___x_1644_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1591_ = v___x_1638_;
v___y_1592_ = v___y_1623_;
v___y_1593_ = v___y_1624_;
v___y_1594_ = v___y_1625_;
v___y_1595_ = v___y_1626_;
v___y_1596_ = v___y_1627_;
v___y_1597_ = v___y_1628_;
v___y_1598_ = v___x_1641_;
v___y_1599_ = v___y_1630_;
v___y_1600_ = v___y_1631_;
v___y_1601_ = v___y_1632_;
v___y_1602_ = v___y_1633_;
v___y_1603_ = v___y_1635_;
v___y_1604_ = v___x_1644_;
goto v___jp_1590_;
}
}
v___jp_1645_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_inc_ref(v___y_1646_);
v___x_1660_ = l_Array_append___redArg(v___y_1646_, v___y_1659_);
lean_dec_ref(v___y_1659_);
lean_inc(v___y_1649_);
lean_inc(v___y_1648_);
v___x_1661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1661_, 0, v___y_1648_);
lean_ctor_set(v___x_1661_, 1, v___y_1649_);
lean_ctor_set(v___x_1661_, 2, v___x_1660_);
if (lean_obj_tag(v___y_1652_) == 1)
{
lean_object* v_val_1662_; lean_object* v___x_1663_; 
v_val_1662_ = lean_ctor_get(v___y_1652_, 0);
lean_inc(v_val_1662_);
lean_dec_ref_known(v___y_1652_, 1);
v___x_1663_ = l_Array_mkArray1___redArg(v_val_1662_);
v___y_1623_ = v___x_1661_;
v___y_1624_ = v___y_1646_;
v___y_1625_ = v___y_1647_;
v___y_1626_ = v___y_1648_;
v___y_1627_ = v___y_1649_;
v___y_1628_ = v___y_1650_;
v___y_1629_ = v___y_1651_;
v___y_1630_ = v___y_1653_;
v___y_1631_ = v___y_1654_;
v___y_1632_ = v___y_1655_;
v___y_1633_ = v___y_1656_;
v___y_1634_ = v___y_1657_;
v___y_1635_ = v___y_1658_;
v___y_1636_ = v___x_1663_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1664_; 
lean_dec(v___y_1652_);
v___x_1664_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1623_ = v___x_1661_;
v___y_1624_ = v___y_1646_;
v___y_1625_ = v___y_1647_;
v___y_1626_ = v___y_1648_;
v___y_1627_ = v___y_1649_;
v___y_1628_ = v___y_1650_;
v___y_1629_ = v___y_1651_;
v___y_1630_ = v___y_1653_;
v___y_1631_ = v___y_1654_;
v___y_1632_ = v___y_1655_;
v___y_1633_ = v___y_1656_;
v___y_1634_ = v___y_1657_;
v___y_1635_ = v___y_1658_;
v___y_1636_ = v___x_1664_;
goto v___jp_1622_;
}
}
v___jp_1665_:
{
lean_object* v_ref_1678_; uint8_t v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v_ref_1678_ = lean_ctor_get(v___y_1676_, 5);
v___x_1679_ = 0;
v___x_1680_ = l_Lean_SourceInfo_fromRef(v_ref_1678_, v___x_1679_);
v___x_1681_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_1682_ = lean_obj_once(&l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
if (lean_obj_tag(v___y_1667_) == 1)
{
lean_object* v_val_1683_; lean_object* v___x_1684_; 
v_val_1683_ = lean_ctor_get(v___y_1667_, 0);
lean_inc(v_val_1683_);
lean_dec_ref_known(v___y_1667_, 1);
v___x_1684_ = l_Array_mkArray1___redArg(v_val_1683_);
v___y_1646_ = v___x_1682_;
v___y_1647_ = v___y_1677_;
v___y_1648_ = v___x_1680_;
v___y_1649_ = v___x_1681_;
v___y_1650_ = v___y_1666_;
v___y_1651_ = v___y_1668_;
v___y_1652_ = v___y_1669_;
v___y_1653_ = v___y_1670_;
v___y_1654_ = v___y_1671_;
v___y_1655_ = v_wds_x3f_1675_;
v___y_1656_ = v___y_1672_;
v___y_1657_ = v___y_1673_;
v___y_1658_ = v___y_1674_;
v___y_1659_ = v___x_1684_;
goto v___jp_1645_;
}
else
{
lean_object* v___x_1685_; 
lean_dec(v___y_1667_);
v___x_1685_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1646_ = v___x_1682_;
v___y_1647_ = v___y_1677_;
v___y_1648_ = v___x_1680_;
v___y_1649_ = v___x_1681_;
v___y_1650_ = v___y_1666_;
v___y_1651_ = v___y_1668_;
v___y_1652_ = v___y_1669_;
v___y_1653_ = v___y_1670_;
v___y_1654_ = v___y_1671_;
v___y_1655_ = v_wds_x3f_1675_;
v___y_1656_ = v___y_1672_;
v___y_1657_ = v___y_1673_;
v___y_1658_ = v___y_1674_;
v___y_1659_ = v___x_1685_;
goto v___jp_1645_;
}
}
v___jp_1686_:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1696_ = lean_unsigned_to_nat(4u);
v___x_1697_ = l_Lean_Syntax_getArg(v_stx_1351_, v___x_1696_);
v___x_1698_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26));
lean_inc(v___x_1697_);
v___x_1699_ = l_Lean_Syntax_isOfKind(v___x_1697_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1700_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1701_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_1702_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_1703_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27));
lean_inc(v___x_1697_);
v___x_1704_ = l_Lean_Syntax_isOfKind(v___x_1697_, v___x_1703_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_dec(v___x_1697_);
lean_dec(v_pkg_x3f_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1689_);
lean_dec(v___y_1688_);
v___x_1705_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1706_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1351_, v___x_1705_, v___y_1694_, v___y_1695_);
lean_dec(v_stx_1351_);
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1707_ = l_Lean_Syntax_getArg(v___x_1697_, v___y_1687_);
v___x_1708_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28));
lean_inc(v___x_1707_);
v___x_1709_ = l_Lean_Syntax_isOfKind(v___x_1707_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_dec(v___x_1707_);
lean_dec(v___x_1697_);
lean_dec(v_pkg_x3f_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1689_);
lean_dec(v___y_1688_);
v___x_1710_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1711_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1351_, v___x_1710_, v___y_1694_, v___y_1695_);
lean_dec(v_stx_1351_);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = l_Lean_Syntax_getArg(v___x_1707_, v___x_1400_);
v___x_1713_ = l_Lean_Syntax_matchesNull(v___x_1712_, v___x_1400_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec(v___x_1707_);
lean_dec(v___x_1697_);
lean_dec(v_pkg_x3f_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1689_);
lean_dec(v___y_1688_);
v___x_1714_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1715_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1351_, v___x_1714_, v___y_1694_, v___y_1695_);
lean_dec(v_stx_1351_);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = l_Lean_Syntax_getArg(v___x_1707_, v___y_1690_);
lean_dec(v___x_1707_);
v___x_1717_ = l_Lean_Syntax_matchesNull(v___x_1716_, v___x_1400_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec(v___x_1697_);
lean_dec(v_pkg_x3f_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1689_);
lean_dec(v___y_1688_);
v___x_1718_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1719_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1351_, v___x_1718_, v___y_1694_, v___y_1695_);
lean_dec(v_stx_1351_);
return v___x_1719_;
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1720_ = l_Lean_Syntax_getArg(v___x_1697_, v___y_1690_);
v___x_1721_ = l_Lean_Syntax_getArg(v___x_1697_, v___y_1691_);
lean_dec(v___x_1697_);
v___x_1722_ = l_Lean_Syntax_isNone(v___x_1721_);
if (v___x_1722_ == 0)
{
uint8_t v___x_1723_; 
lean_inc(v___x_1721_);
v___x_1723_ = l_Lean_Syntax_matchesNull(v___x_1721_, v___y_1690_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_dec(v___x_1721_);
lean_dec(v___x_1720_);
lean_dec(v_pkg_x3f_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1689_);
lean_dec(v___y_1688_);
v___x_1724_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1725_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1351_, v___x_1724_, v___y_1694_, v___y_1695_);
lean_dec(v_stx_1351_);
return v___x_1725_;
}
else
{
lean_object* v_wds_x3f_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_wds_x3f_1726_ = l_Lean_Syntax_getArg(v___x_1721_, v___x_1400_);
lean_dec(v___x_1721_);
v___x_1727_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_1726_);
v___x_1728_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1726_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v_wds_x3f_1726_);
lean_dec(v___x_1720_);
lean_dec(v_pkg_x3f_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1689_);
lean_dec(v___y_1688_);
v___x_1729_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1730_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1351_, v___x_1729_, v___y_1694_, v___y_1695_);
lean_dec(v_stx_1351_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; 
lean_dec(v_stx_1351_);
v___x_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_wds_x3f_1726_);
v___y_1524_ = v___x_1708_;
v___y_1525_ = v___x_1703_;
v___y_1526_ = v___x_1701_;
v___y_1527_ = v___y_1688_;
v___y_1528_ = v_pkg_x3f_1693_;
v___y_1529_ = v___y_1689_;
v___y_1530_ = v___y_1690_;
v___y_1531_ = v___x_1720_;
v___y_1532_ = v___x_1702_;
v___y_1533_ = v___x_1699_;
v___y_1534_ = v___y_1692_;
v___y_1535_ = v___x_1700_;
v_wds_x3f_1536_ = v___x_1731_;
v___y_1537_ = v___y_1694_;
v___y_1538_ = v___y_1695_;
goto v___jp_1523_;
}
}
}
else
{
lean_object* v___x_1732_; 
lean_dec(v___x_1721_);
lean_dec(v_stx_1351_);
v___x_1732_ = lean_box(0);
v___y_1524_ = v___x_1708_;
v___y_1525_ = v___x_1703_;
v___y_1526_ = v___x_1701_;
v___y_1527_ = v___y_1688_;
v___y_1528_ = v_pkg_x3f_1693_;
v___y_1529_ = v___y_1689_;
v___y_1530_ = v___y_1690_;
v___y_1531_ = v___x_1720_;
v___y_1532_ = v___x_1702_;
v___y_1533_ = v___x_1699_;
v___y_1534_ = v___y_1692_;
v___y_1535_ = v___x_1700_;
v_wds_x3f_1536_ = v___x_1732_;
v___y_1537_ = v___y_1694_;
v___y_1538_ = v___y_1695_;
goto v___jp_1523_;
}
}
}
}
}
}
else
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1733_ = l_Lean_Syntax_getArg(v___x_1697_, v___x_1400_);
v___x_1734_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1735_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_1736_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29));
v___x_1737_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30));
lean_inc(v___x_1733_);
v___x_1738_ = l_Lean_Syntax_isOfKind(v___x_1733_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec(v___x_1733_);
lean_dec(v___x_1697_);
lean_dec(v_pkg_x3f_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1689_);
lean_dec(v___y_1688_);
v___x_1739_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1740_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1351_, v___x_1739_, v___y_1694_, v___y_1695_);
lean_dec(v_stx_1351_);
return v___x_1740_;
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1741_ = l_Lean_Syntax_getArg(v___x_1733_, v___y_1690_);
lean_dec(v___x_1733_);
v___x_1742_ = l_Lean_Syntax_getArg(v___x_1697_, v___y_1690_);
lean_dec(v___x_1697_);
v___x_1743_ = l_Lean_Syntax_isNone(v___x_1742_);
if (v___x_1743_ == 0)
{
uint8_t v___x_1744_; 
lean_inc(v___x_1742_);
v___x_1744_ = l_Lean_Syntax_matchesNull(v___x_1742_, v___y_1690_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_dec(v___x_1742_);
lean_dec(v___x_1741_);
lean_dec(v_pkg_x3f_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1689_);
lean_dec(v___y_1688_);
v___x_1745_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1746_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1351_, v___x_1745_, v___y_1694_, v___y_1695_);
lean_dec(v_stx_1351_);
return v___x_1746_;
}
else
{
lean_object* v_wds_x3f_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v_wds_x3f_1747_ = l_Lean_Syntax_getArg(v___x_1742_, v___x_1400_);
lean_dec(v___x_1742_);
v___x_1748_ = ((lean_object*)(l_Lake_DSL_mkConfigDef___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_1747_);
v___x_1749_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1747_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v_wds_x3f_1747_);
lean_dec(v___x_1741_);
lean_dec(v_pkg_x3f_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1689_);
lean_dec(v___y_1688_);
v___x_1750_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1751_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1351_, v___x_1750_, v___y_1694_, v___y_1695_);
lean_dec(v_stx_1351_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; 
lean_dec(v_stx_1351_);
v___x_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_wds_x3f_1747_);
v___y_1666_ = v___x_1734_;
v___y_1667_ = v___y_1688_;
v___y_1668_ = v_pkg_x3f_1693_;
v___y_1669_ = v___y_1689_;
v___y_1670_ = v___x_1741_;
v___y_1671_ = v___x_1735_;
v___y_1672_ = v___x_1736_;
v___y_1673_ = v___y_1692_;
v___y_1674_ = v___x_1737_;
v_wds_x3f_1675_ = v___x_1752_;
v___y_1676_ = v___y_1694_;
v___y_1677_ = v___y_1695_;
goto v___jp_1665_;
}
}
}
else
{
lean_object* v___x_1753_; 
lean_dec(v___x_1742_);
lean_dec(v_stx_1351_);
v___x_1753_ = lean_box(0);
v___y_1666_ = v___x_1734_;
v___y_1667_ = v___y_1688_;
v___y_1668_ = v_pkg_x3f_1693_;
v___y_1669_ = v___y_1689_;
v___y_1670_ = v___x_1741_;
v___y_1671_ = v___x_1735_;
v___y_1672_ = v___x_1736_;
v___y_1673_ = v___y_1692_;
v___y_1674_ = v___x_1737_;
v_wds_x3f_1675_ = v___x_1753_;
v___y_1676_ = v___y_1694_;
v___y_1677_ = v___y_1695_;
goto v___jp_1665_;
}
}
}
}
v___jp_1754_:
{
lean_object* v___x_1760_; lean_object* v_kw_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1760_ = lean_unsigned_to_nat(2u);
v_kw_1761_ = l_Lean_Syntax_getArg(v_stx_1351_, v___x_1760_);
v___x_1762_ = lean_unsigned_to_nat(3u);
v___x_1763_ = l_Lean_Syntax_getArg(v_stx_1351_, v___x_1762_);
v___x_1764_ = l_Lean_Syntax_isNone(v___x_1763_);
if (v___x_1764_ == 0)
{
uint8_t v___x_1765_; 
lean_inc(v___x_1763_);
v___x_1765_ = l_Lean_Syntax_matchesNull(v___x_1763_, v___y_1756_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec(v___x_1763_);
lean_dec(v_kw_1761_);
lean_dec(v_attrs_x3f_1757_);
lean_dec(v___y_1755_);
v___x_1766_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1767_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1351_, v___x_1766_, v___y_1758_, v___y_1759_);
lean_dec(v_stx_1351_);
return v___x_1767_;
}
else
{
lean_object* v_pkg_x3f_1768_; lean_object* v___x_1769_; 
v_pkg_x3f_1768_ = l_Lean_Syntax_getArg(v___x_1763_, v___x_1400_);
lean_dec(v___x_1763_);
v___x_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_pkg_x3f_1768_);
v___y_1687_ = v___x_1760_;
v___y_1688_ = v___y_1755_;
v___y_1689_ = v_attrs_x3f_1757_;
v___y_1690_ = v___y_1756_;
v___y_1691_ = v___x_1762_;
v___y_1692_ = v_kw_1761_;
v_pkg_x3f_1693_ = v___x_1769_;
v___y_1694_ = v___y_1758_;
v___y_1695_ = v___y_1759_;
goto v___jp_1686_;
}
}
else
{
lean_object* v___x_1770_; 
lean_dec(v___x_1763_);
v___x_1770_ = lean_box(0);
v___y_1687_ = v___x_1760_;
v___y_1688_ = v___y_1755_;
v___y_1689_ = v_attrs_x3f_1757_;
v___y_1690_ = v___y_1756_;
v___y_1691_ = v___x_1762_;
v___y_1692_ = v_kw_1761_;
v_pkg_x3f_1693_ = v___x_1770_;
v___y_1694_ = v___y_1758_;
v___y_1695_ = v___y_1759_;
goto v___jp_1686_;
}
}
v___jp_1771_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1776_ = l_Lean_Syntax_getArg(v_stx_1351_, v___x_1775_);
v___x_1777_ = l_Lean_Syntax_isNone(v___x_1776_);
if (v___x_1777_ == 0)
{
uint8_t v___x_1778_; 
lean_inc(v___x_1776_);
v___x_1778_ = l_Lean_Syntax_matchesNull(v___x_1776_, v___x_1775_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v___x_1776_);
lean_dec(v_doc_x3f_1772_);
v___x_1779_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1780_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1351_, v___x_1779_, v___y_1773_, v___y_1774_);
lean_dec(v_stx_1351_);
return v___x_1780_;
}
else
{
lean_object* v_attrs_x3f_1781_; lean_object* v___x_1782_; 
v_attrs_x3f_1781_ = l_Lean_Syntax_getArg(v___x_1776_, v___x_1400_);
lean_dec(v___x_1776_);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_attrs_x3f_1781_);
v___y_1755_ = v_doc_x3f_1772_;
v___y_1756_ = v___x_1775_;
v_attrs_x3f_1757_ = v___x_1782_;
v___y_1758_ = v___y_1773_;
v___y_1759_ = v___y_1774_;
goto v___jp_1754_;
}
}
else
{
lean_object* v___x_1783_; 
lean_dec(v___x_1776_);
v___x_1783_ = lean_box(0);
v___y_1755_ = v_doc_x3f_1772_;
v___y_1756_ = v___x_1775_;
v_attrs_x3f_1757_ = v___x_1783_;
v___y_1758_ = v___y_1773_;
v___y_1759_ = v___y_1774_;
goto v___jp_1754_;
}
}
}
v___jp_1354_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_inc_ref(v___y_1368_);
v___x_1371_ = l_Array_append___redArg(v___y_1368_, v___y_1370_);
lean_dec_ref(v___y_1370_);
lean_inc(v___y_1359_);
lean_inc_n(v___y_1357_, 3);
v___x_1372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1372_, 0, v___y_1357_);
lean_ctor_set(v___x_1372_, 1, v___y_1359_);
lean_ctor_set(v___x_1372_, 2, v___x_1371_);
lean_inc(v___y_1365_);
v___x_1373_ = l_Lean_Syntax_node4(v___y_1357_, v___y_1365_, v___y_1362_, v___y_1358_, v___y_1363_, v___x_1372_);
v___x_1374_ = l_Lean_Syntax_node5(v___y_1357_, v___y_1356_, v___y_1360_, v___y_1366_, v___y_1361_, v___x_1373_, v___y_1369_);
v___x_1375_ = l_Lean_Syntax_node2(v___y_1357_, v___y_1364_, v___y_1355_, v___x_1374_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
lean_ctor_set(v___x_1376_, 1, v___y_1367_);
return v___x_1376_;
}
v___jp_1378_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_inc_ref(v___y_1386_);
v___x_1392_ = l_Array_append___redArg(v___y_1386_, v___y_1391_);
lean_dec_ref(v___y_1391_);
lean_inc(v___y_1388_);
lean_inc_n(v___y_1389_, 2);
v___x_1393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1393_, 0, v___y_1389_);
lean_ctor_set(v___x_1393_, 1, v___y_1388_);
lean_ctor_set(v___x_1393_, 2, v___x_1392_);
v___x_1394_ = l_Lean_Syntax_node4(v___y_1389_, v___y_1384_, v___y_1379_, v___y_1385_, v___y_1382_, v___x_1393_);
v___x_1395_ = l_Lean_Syntax_node5(v___y_1389_, v___x_1377_, v___y_1383_, v___y_1381_, v___y_1380_, v___y_1390_, v___x_1394_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
lean_ctor_set(v___x_1396_, 1, v___y_1387_);
return v___x_1396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed(lean_object* v_stx_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(v_stx_1793_, v_a_1794_, v_a_1795_);
lean_dec_ref(v_a_1794_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1(){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1802_ = l_Lean_Elab_macroAttribute;
v___x_1803_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1));
v___x_1804_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1));
v___x_1805_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed), 3, 0);
v___x_1806_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1802_, v___x_1803_, v___x_1804_, v___x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___boxed(lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
return v_res_1808_;
}
}
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Extensions(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
