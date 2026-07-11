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
uint8_t lean_bool_not(uint8_t);
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
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value;
static const lean_array_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "baseName"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_value),LEAN_SCALAR_PTR_LITERAL(110, 15, 203, 48, 91, 80, 65, 181)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "origName"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_value),LEAN_SCALAR_PTR_LITERAL(60, 90, 152, 77, 27, 27, 68, 80)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "keyName"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_value),LEAN_SCALAR_PTR_LITERAL(25, 96, 4, 27, 96, 164, 24, 20)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value),LEAN_SCALAR_PTR_LITERAL(207, 146, 87, 28, 198, 178, 209, 199)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 9, .m_data = "«package»"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "package"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value_aux_0),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value),LEAN_SCALAR_PTR_LITERAL(35, 98, 18, 79, 25, 208, 83, 100)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PackageConfig"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value_aux_0),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value),LEAN_SCALAR_PTR_LITERAL(14, 50, 33, 106, 4, 142, 225, 217)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
lean_dec_ref_known(v___x_121_, 1);
if (lean_obj_tag(v_val_123_) == 1)
{
uint8_t v_v_124_; 
v_v_124_ = lean_ctor_get_uint8(v_val_123_, 0);
lean_dec_ref_known(v_val_123_, 0);
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
lean_object* v___x_139_; lean_object* v_scopes_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v_opts_143_; lean_object* v___x_144_; uint8_t v___x_145_; uint8_t v___x_146_; 
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
v___x_146_ = lean_bool_not(v___x_145_);
if (v___x_146_ == 0)
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
else
{
lean_object* v___x_166_; 
lean_dec(v_macroStack_136_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v_msgData_135_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_167_, lean_object* v_macroStack_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_167_, v_macroStack_168_, v___y_169_);
lean_dec(v___y_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(lean_object* v_msg_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Elab_Command_getRef___redArg(v___y_173_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v_macroStack_178_; lean_object* v___x_179_; lean_object* v_a_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_191_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_176_, 1);
v_macroStack_178_ = lean_ctor_get(v___y_173_, 4);
v___x_179_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msg_172_, v___y_174_);
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref(v___x_179_);
v___x_181_ = l_Lean_Elab_getBetterRef(v_a_177_, v_macroStack_178_);
lean_dec(v_a_177_);
lean_inc(v_macroStack_178_);
v___x_182_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_a_180_, v_macroStack_178_, v___y_174_);
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_191_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_181_);
lean_ctor_set(v___x_187_, 1, v_a_183_);
if (v_isShared_186_ == 0)
{
lean_ctor_set_tag(v___x_185_, 1);
lean_ctor_set(v___x_185_, 0, v___x_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec_ref(v_msg_172_);
v_a_192_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_176_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_176_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg___boxed(lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(lean_object* v_ref_205_, lean_object* v_msg_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Elab_Command_getRef___redArg(v___y_207_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v_fileName_212_; lean_object* v_fileMap_213_; lean_object* v_currRecDepth_214_; lean_object* v_cmdPos_215_; lean_object* v_macroStack_216_; lean_object* v_quotContext_x3f_217_; lean_object* v_currMacroScope_218_; lean_object* v_snap_x3f_219_; lean_object* v_cancelTk_x3f_220_; uint8_t v_suppressElabErrors_221_; lean_object* v_ref_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_210_, 1);
v_fileName_212_ = lean_ctor_get(v___y_207_, 0);
v_fileMap_213_ = lean_ctor_get(v___y_207_, 1);
v_currRecDepth_214_ = lean_ctor_get(v___y_207_, 2);
v_cmdPos_215_ = lean_ctor_get(v___y_207_, 3);
v_macroStack_216_ = lean_ctor_get(v___y_207_, 4);
v_quotContext_x3f_217_ = lean_ctor_get(v___y_207_, 5);
v_currMacroScope_218_ = lean_ctor_get(v___y_207_, 6);
v_snap_x3f_219_ = lean_ctor_get(v___y_207_, 8);
v_cancelTk_x3f_220_ = lean_ctor_get(v___y_207_, 9);
v_suppressElabErrors_221_ = lean_ctor_get_uint8(v___y_207_, sizeof(void*)*10);
v_ref_222_ = l_Lean_replaceRef(v_ref_205_, v_a_211_);
lean_dec(v_a_211_);
lean_inc(v_cancelTk_x3f_220_);
lean_inc(v_snap_x3f_219_);
lean_inc(v_currMacroScope_218_);
lean_inc(v_quotContext_x3f_217_);
lean_inc(v_macroStack_216_);
lean_inc(v_cmdPos_215_);
lean_inc(v_currRecDepth_214_);
lean_inc_ref(v_fileMap_213_);
lean_inc_ref(v_fileName_212_);
v___x_223_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_223_, 0, v_fileName_212_);
lean_ctor_set(v___x_223_, 1, v_fileMap_213_);
lean_ctor_set(v___x_223_, 2, v_currRecDepth_214_);
lean_ctor_set(v___x_223_, 3, v_cmdPos_215_);
lean_ctor_set(v___x_223_, 4, v_macroStack_216_);
lean_ctor_set(v___x_223_, 5, v_quotContext_x3f_217_);
lean_ctor_set(v___x_223_, 6, v_currMacroScope_218_);
lean_ctor_set(v___x_223_, 7, v_ref_222_);
lean_ctor_set(v___x_223_, 8, v_snap_x3f_219_);
lean_ctor_set(v___x_223_, 9, v_cancelTk_x3f_220_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*10, v_suppressElabErrors_221_);
v___x_224_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_206_, v___x_223_, v___y_208_);
lean_dec_ref_known(v___x_223_, 10);
return v___x_224_;
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec_ref(v_msg_206_);
v_a_225_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_210_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_210_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg___boxed(lean_object* v_ref_233_, lean_object* v_msg_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_233_, v_msg_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v_ref_233_);
return v_res_238_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4(void){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Array_mkArray0(lean_box(0));
return v___x_244_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23));
v___x_273_ = l_Lean_stringToMessageData(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(lean_object* v_tyName_301_, lean_object* v_id_302_, lean_object* v_ty_303_, lean_object* v_config_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___x_393_; lean_object* v_whereInfo_395_; lean_object* v_fs_396_; lean_object* v_wds_x3f_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_393_ = l_Lake_PackageConfig_instConfigInfo;
v___x_426_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22));
lean_inc(v_config_304_);
v___x_427_ = l_Lean_Syntax_isOfKind(v_config_304_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec(v_ty_303_);
lean_dec(v_id_302_);
lean_dec(v_tyName_301_);
v___x_428_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_429_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_304_, v___x_428_, v_a_305_, v_a_306_);
lean_dec(v_config_304_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = l_Lean_Syntax_getArg(v_config_304_, v___x_430_);
lean_inc(v___x_431_);
v___x_432_ = l_Lean_Syntax_matchesNull(v___x_431_, v___x_430_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_431_);
v___x_434_ = l_Lean_Syntax_matchesNull(v___x_431_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v___x_431_);
lean_dec(v_ty_303_);
lean_dec(v_id_302_);
lean_dec(v_tyName_301_);
v___x_435_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_436_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_304_, v___x_435_, v_a_305_, v_a_306_);
lean_dec(v_config_304_);
return v___x_436_;
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_437_ = l_Lean_Syntax_getArg(v___x_431_, v___x_430_);
lean_dec(v___x_431_);
v___x_438_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26));
lean_inc(v___x_437_);
v___x_439_ = l_Lean_Syntax_isOfKind(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28));
lean_inc(v___x_437_);
v___x_441_ = l_Lean_Syntax_isOfKind(v___x_437_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec(v___x_437_);
lean_dec(v_ty_303_);
lean_dec(v_id_302_);
lean_dec(v_tyName_301_);
v___x_442_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_443_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_304_, v___x_442_, v_a_305_, v_a_306_);
lean_dec(v_config_304_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_444_ = l_Lean_Syntax_getArg(v___x_437_, v___x_430_);
v___x_445_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30));
lean_inc(v___x_444_);
v___x_446_ = l_Lean_Syntax_isOfKind(v___x_444_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v___x_444_);
lean_dec(v___x_437_);
lean_dec(v_ty_303_);
lean_dec(v_id_302_);
lean_dec(v_tyName_301_);
v___x_447_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_448_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_304_, v___x_447_, v_a_305_, v_a_306_);
lean_dec(v_config_304_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_449_ = l_Lean_Syntax_getArg(v___x_444_, v___x_433_);
v___x_450_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32));
lean_inc(v___x_449_);
v___x_451_ = l_Lean_Syntax_isOfKind(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec(v___x_449_);
lean_dec(v___x_444_);
lean_dec(v___x_437_);
lean_dec(v_ty_303_);
lean_dec(v_id_302_);
lean_dec(v_tyName_301_);
v___x_452_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_453_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_304_, v___x_452_, v_a_305_, v_a_306_);
lean_dec(v_config_304_);
return v___x_453_;
}
else
{
lean_object* v_tk_454_; lean_object* v___x_455_; lean_object* v_wds_x3f_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___x_463_; uint8_t v___x_464_; 
v_tk_454_ = l_Lean_Syntax_getArg(v___x_444_, v___x_430_);
lean_dec(v___x_444_);
v___x_455_ = l_Lean_Syntax_getArg(v___x_449_, v___x_430_);
lean_dec(v___x_449_);
v___x_463_ = l_Lean_Syntax_getArg(v___x_437_, v___x_433_);
lean_dec(v___x_437_);
v___x_464_ = l_Lean_Syntax_isNone(v___x_463_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; 
lean_inc(v___x_463_);
v___x_465_ = l_Lean_Syntax_matchesNull(v___x_463_, v___x_433_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec(v___x_463_);
lean_dec(v___x_455_);
lean_dec(v_tk_454_);
lean_dec(v_ty_303_);
lean_dec(v_id_302_);
lean_dec(v_tyName_301_);
v___x_466_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_467_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_304_, v___x_466_, v_a_305_, v_a_306_);
lean_dec(v_config_304_);
return v___x_467_;
}
else
{
lean_object* v_wds_x3f_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_wds_x3f_468_ = l_Lean_Syntax_getArg(v___x_463_, v___x_430_);
lean_dec(v___x_463_);
v___x_469_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_468_);
v___x_470_ = l_Lean_Syntax_isOfKind(v_wds_x3f_468_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec(v_wds_x3f_468_);
lean_dec(v___x_455_);
lean_dec(v_tk_454_);
lean_dec(v_ty_303_);
lean_dec(v_id_302_);
lean_dec(v_tyName_301_);
v___x_471_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_472_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_304_, v___x_471_, v_a_305_, v_a_306_);
lean_dec(v_config_304_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; 
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v_wds_x3f_468_);
v_wds_x3f_457_ = v___x_473_;
v___y_458_ = v_a_305_;
v___y_459_ = v_a_306_;
goto v___jp_456_;
}
}
}
else
{
lean_object* v___x_474_; 
lean_dec(v___x_463_);
v___x_474_ = lean_box(0);
v_wds_x3f_457_ = v___x_474_;
v___y_458_ = v_a_305_;
v___y_459_ = v_a_306_;
goto v___jp_456_;
}
v___jp_456_:
{
lean_object* v_fs_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_fs_460_ = l_Lean_Syntax_getArgs(v___x_455_);
lean_dec(v___x_455_);
v___x_461_ = l_Lean_Syntax_getHeadInfo(v_tk_454_);
lean_dec(v_tk_454_);
v___x_462_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_460_);
lean_dec_ref(v_fs_460_);
v_whereInfo_395_ = v___x_461_;
v_fs_396_ = v___x_462_;
v_wds_x3f_397_ = v_wds_x3f_457_;
v___y_398_ = v___y_458_;
v___y_399_ = v___y_459_;
goto v___jp_394_;
}
}
}
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_475_ = l_Lean_Syntax_getArg(v___x_437_, v___x_433_);
v___x_476_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32));
lean_inc(v___x_475_);
v___x_477_ = l_Lean_Syntax_isOfKind(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v___x_475_);
lean_dec(v___x_437_);
lean_dec(v_ty_303_);
lean_dec(v_id_302_);
lean_dec(v_tyName_301_);
v___x_478_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_479_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_304_, v___x_478_, v_a_305_, v_a_306_);
lean_dec(v_config_304_);
return v___x_479_;
}
else
{
lean_object* v_tk_480_; lean_object* v___x_481_; lean_object* v_wds_x3f_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v_tk_480_ = l_Lean_Syntax_getArg(v___x_437_, v___x_430_);
v___x_481_ = l_Lean_Syntax_getArg(v___x_475_, v___x_430_);
lean_dec(v___x_475_);
v___x_489_ = lean_unsigned_to_nat(2u);
v___x_490_ = l_Lean_Syntax_getArg(v___x_437_, v___x_489_);
lean_dec(v___x_437_);
v___x_491_ = l_Lean_Syntax_isNone(v___x_490_);
if (v___x_491_ == 0)
{
uint8_t v___x_492_; 
lean_inc(v___x_490_);
v___x_492_ = l_Lean_Syntax_matchesNull(v___x_490_, v___x_433_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec(v___x_490_);
lean_dec(v___x_481_);
lean_dec(v_tk_480_);
lean_dec(v_ty_303_);
lean_dec(v_id_302_);
lean_dec(v_tyName_301_);
v___x_493_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_494_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_304_, v___x_493_, v_a_305_, v_a_306_);
lean_dec(v_config_304_);
return v___x_494_;
}
else
{
lean_object* v_wds_x3f_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_wds_x3f_495_ = l_Lean_Syntax_getArg(v___x_490_, v___x_430_);
lean_dec(v___x_490_);
v___x_496_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_495_);
v___x_497_ = l_Lean_Syntax_isOfKind(v_wds_x3f_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v_wds_x3f_495_);
lean_dec(v___x_481_);
lean_dec(v_tk_480_);
lean_dec(v_ty_303_);
lean_dec(v_id_302_);
lean_dec(v_tyName_301_);
v___x_498_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_499_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_304_, v___x_498_, v_a_305_, v_a_306_);
lean_dec(v_config_304_);
return v___x_499_;
}
else
{
lean_object* v___x_500_; 
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v_wds_x3f_495_);
v_wds_x3f_483_ = v___x_500_;
v___y_484_ = v_a_305_;
v___y_485_ = v_a_306_;
goto v___jp_482_;
}
}
}
else
{
lean_object* v___x_501_; 
lean_dec(v___x_490_);
v___x_501_ = lean_box(0);
v_wds_x3f_483_ = v___x_501_;
v___y_484_ = v_a_305_;
v___y_485_ = v_a_306_;
goto v___jp_482_;
}
v___jp_482_:
{
lean_object* v_fs_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_fs_486_ = l_Lean_Syntax_getArgs(v___x_481_);
lean_dec(v___x_481_);
v___x_487_ = l_Lean_Syntax_getHeadInfo(v_tk_480_);
lean_dec(v_tk_480_);
v___x_488_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_486_);
lean_dec_ref(v_fs_486_);
v_whereInfo_395_ = v___x_487_;
v_fs_396_ = v___x_488_;
v_wds_x3f_397_ = v_wds_x3f_483_;
v___y_398_ = v___y_484_;
v___y_399_ = v___y_485_;
goto v___jp_394_;
}
}
}
}
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v___x_431_);
v___x_502_ = lean_box(2);
v___x_503_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
v___x_504_ = lean_box(0);
v_whereInfo_395_ = v___x_502_;
v_fs_396_ = v___x_503_;
v_wds_x3f_397_ = v___x_504_;
v___y_398_ = v_a_305_;
v___y_399_ = v_a_306_;
goto v___jp_394_;
}
}
v___jp_308_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_317_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_316_, 5);
lean_inc_ref_n(v___y_315_, 6);
lean_inc_ref_n(v___y_311_, 6);
v___x_318_ = l_Lean_Name_mkStr4(v___y_311_, v___y_315_, v___y_316_, v___x_317_);
v___x_319_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_320_ = l_Lean_Name_mkStr4(v___y_311_, v___y_315_, v___y_316_, v___x_319_);
v___x_321_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_322_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___y_309_, 8);
v___x_323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_323_, 0, v___y_309_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_322_);
lean_inc_ref_n(v___x_323_, 8);
v___x_324_ = l_Lean_Syntax_node7(v___y_309_, v___x_320_, v___x_323_, v___x_323_, v___x_323_, v___x_323_, v___x_323_, v___x_323_, v___x_323_);
v___x_325_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5));
v___x_326_ = l_Lean_Name_mkStr4(v___y_311_, v___y_315_, v___y_316_, v___x_325_);
v___x_327_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6));
v___x_328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_328_, 0, v___y_309_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_330_ = l_Lean_Name_mkStr4(v___y_311_, v___y_315_, v___y_316_, v___x_329_);
v___x_331_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
lean_inc_n(v___y_314_, 2);
v___x_332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_332_, 0, v___y_314_);
lean_ctor_set(v___x_332_, 1, v___x_321_);
lean_ctor_set(v___x_332_, 2, v___x_331_);
v___x_333_ = lean_unsigned_to_nat(2u);
v___x_334_ = lean_mk_empty_array_with_capacity(v___x_333_);
v___x_335_ = lean_array_push(v___x_334_, v_id_302_);
v___x_336_ = lean_array_push(v___x_335_, v___x_332_);
v___x_337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_337_, 0, v___y_314_);
lean_ctor_set(v___x_337_, 1, v___x_330_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
v___x_338_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_339_ = l_Lean_Name_mkStr4(v___y_311_, v___y_315_, v___y_316_, v___x_338_);
v___x_340_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_341_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_342_ = l_Lean_Name_mkStr4(v___y_311_, v___y_315_, v___x_340_, v___x_341_);
v___x_343_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_344_, 0, v___y_309_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_Syntax_node2(v___y_309_, v___x_342_, v___x_344_, v_ty_303_);
v___x_346_ = l_Lean_Syntax_node1(v___y_309_, v___x_321_, v___x_345_);
v___x_347_ = l_Lean_Syntax_node2(v___y_309_, v___x_339_, v___x_323_, v___x_346_);
v___x_348_ = l_Lean_Syntax_node5(v___y_309_, v___x_326_, v___x_328_, v___x_337_, v___x_347_, v___y_310_, v___x_323_);
v___x_349_ = l_Lean_Syntax_node2(v___y_309_, v___x_318_, v___x_324_, v___x_348_);
lean_inc(v___x_349_);
v___x_350_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_350_, 0, v___x_349_);
v___x_351_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_config_304_, v___x_349_, v___x_350_, v___y_313_, v___y_312_);
return v___x_351_;
}
v___jp_352_:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Elab_Command_getRef___redArg(v___y_357_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_364_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
v___x_364_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_357_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_quotContext_x3f_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; 
lean_dec_ref_known(v___x_364_, 1);
v_quotContext_x3f_365_ = lean_ctor_get(v___y_357_, 5);
v___x_366_ = l_Lean_mkOptionalNode(v___y_361_);
v___x_367_ = lean_unsigned_to_nat(3u);
v___x_368_ = lean_mk_empty_array_with_capacity(v___x_367_);
v___x_369_ = lean_array_push(v___x_368_, v___y_360_);
v___x_370_ = lean_array_push(v___x_369_, v___y_356_);
v___x_371_ = lean_array_push(v___x_370_, v___x_366_);
v___x_372_ = lean_box(2);
lean_inc(v___y_353_);
v___x_373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___y_353_);
lean_ctor_set(v___x_373_, 2, v___x_371_);
v___x_374_ = 0;
v___x_375_ = l_Lean_SourceInfo_fromRef(v_a_363_, v___x_374_);
lean_dec(v_a_363_);
if (lean_obj_tag(v_quotContext_x3f_365_) == 0)
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_355_);
lean_dec_ref(v___x_376_);
v___y_309_ = v___x_375_;
v___y_310_ = v___x_373_;
v___y_311_ = v___y_354_;
v___y_312_ = v___y_355_;
v___y_313_ = v___y_357_;
v___y_314_ = v___x_372_;
v___y_315_ = v___y_358_;
v___y_316_ = v___y_359_;
goto v___jp_308_;
}
else
{
v___y_309_ = v___x_375_;
v___y_310_ = v___x_373_;
v___y_311_ = v___y_354_;
v___y_312_ = v___y_355_;
v___y_313_ = v___y_357_;
v___y_314_ = v___x_372_;
v___y_315_ = v___y_358_;
v___y_316_ = v___y_359_;
goto v___jp_308_;
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec(v_a_363_);
lean_dec(v___y_361_);
lean_dec(v___y_360_);
lean_dec(v___y_356_);
lean_dec(v_config_304_);
lean_dec(v_ty_303_);
lean_dec(v_id_302_);
v_a_377_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_364_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_364_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v___y_361_);
lean_dec(v___y_360_);
lean_dec(v___y_356_);
lean_dec(v_config_304_);
lean_dec(v_ty_303_);
lean_dec(v_id_302_);
v_a_385_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_362_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_362_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
v___jp_394_:
{
lean_object* v_fieldMap_400_; lean_object* v___x_401_; 
v_fieldMap_400_ = lean_ctor_get(v___x_393_, 1);
v___x_401_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_301_, v_fieldMap_400_, v_fs_396_, v___y_398_, v___y_399_);
lean_dec_ref(v_fs_396_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; lean_object* v_whereTk_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 1);
v___x_403_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13));
v_whereTk_404_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_whereTk_404_, 0, v_whereInfo_395_);
lean_ctor_set(v_whereTk_404_, 1, v___x_403_);
v___x_405_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_406_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_407_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_408_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18));
if (lean_obj_tag(v_wds_x3f_397_) == 0)
{
lean_object* v___x_409_; 
v___x_409_ = lean_box(0);
v___y_353_ = v___x_408_;
v___y_354_ = v___x_405_;
v___y_355_ = v___y_399_;
v___y_356_ = v_a_402_;
v___y_357_ = v___y_398_;
v___y_358_ = v___x_406_;
v___y_359_ = v___x_407_;
v___y_360_ = v_whereTk_404_;
v___y_361_ = v___x_409_;
goto v___jp_352_;
}
else
{
lean_object* v_val_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
v_val_410_ = lean_ctor_get(v_wds_x3f_397_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v_wds_x3f_397_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v_wds_x3f_397_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_val_410_);
lean_dec(v_wds_x3f_397_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_val_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
v___y_353_ = v___x_408_;
v___y_354_ = v___x_405_;
v___y_355_ = v___y_399_;
v___y_356_ = v_a_402_;
v___y_357_ = v___y_398_;
v___y_358_ = v___x_406_;
v___y_359_ = v___x_407_;
v___y_360_ = v_whereTk_404_;
v___y_361_ = v___x_415_;
goto v___jp_352_;
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec(v_wds_x3f_397_);
lean_dec(v_whereInfo_395_);
lean_dec(v_config_304_);
lean_dec(v_ty_303_);
lean_dec(v_id_302_);
v_a_418_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_401_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_401_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___boxed(lean_object* v_tyName_505_, lean_object* v_id_506_, lean_object* v_ty_507_, lean_object* v_config_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v_tyName_505_, v_id_506_, v_ty_507_, v_config_508_, v_a_509_, v_a_510_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
return v_res_512_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13));
v___x_535_ = l_Lean_stringToMessageData(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19));
v___x_542_ = l_String_toRawSubstring_x27(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34));
v___x_565_ = l_String_toRawSubstring_x27(v___x_564_);
return v___x_565_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40));
v___x_573_ = l_String_toRawSubstring_x27(v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43));
v___x_578_ = l_String_toRawSubstring_x27(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46));
v___x_583_ = l_String_toRawSubstring_x27(v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53));
v___x_592_ = l_String_toRawSubstring_x27(v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65));
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
lean_dec(v_stx_616_);
return v___x_691_;
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___y_698_; lean_object* v___y_699_; uint8_t v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; uint8_t v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v_a_825_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; uint8_t v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v_a_858_; lean_object* v___y_941_; lean_object* v___y_942_; uint8_t v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v_a_957_; lean_object* v___y_1007_; lean_object* v___y_1008_; uint8_t v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1059_; uint8_t v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v_a_1069_; lean_object* v_kw_1097_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v_nameStx_x3f_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = l_Lean_Syntax_getArg(v_stx_616_, v___x_692_);
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = l_Lean_Syntax_getArg(v_stx_616_, v___x_694_);
v___x_696_ = lean_unsigned_to_nat(2u);
v_kw_1097_ = l_Lean_Syntax_getArg(v_stx_616_, v___x_696_);
v___x_1184_ = lean_unsigned_to_nat(3u);
v___x_1185_ = l_Lean_Syntax_getArg(v_stx_616_, v___x_1184_);
v___x_1186_ = l_Lean_Syntax_isNone(v___x_1185_);
if (v___x_1186_ == 0)
{
uint8_t v___x_1187_; 
lean_inc(v___x_1185_);
v___x_1187_ = l_Lean_Syntax_matchesNull(v___x_1185_, v___x_694_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec(v___x_1185_);
lean_dec(v_kw_1097_);
lean_dec(v___x_695_);
lean_dec(v___x_693_);
v___x_1188_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
v___x_1189_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_616_, v___x_1188_, v_a_617_, v_a_618_);
lean_dec(v_stx_616_);
return v___x_1189_;
}
else
{
lean_object* v_nameStx_x3f_1190_; lean_object* v___x_1191_; 
v_nameStx_x3f_1190_ = l_Lean_Syntax_getArg(v___x_1185_, v___x_692_);
lean_dec(v___x_1185_);
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_nameStx_x3f_1190_);
v_nameStx_x3f_1169_ = v___x_1191_;
v___y_1170_ = v_a_617_;
v___y_1171_ = v_a_618_;
goto v___jp_1168_;
}
}
else
{
lean_object* v___x_1192_; 
lean_dec(v___x_1185_);
v___x_1192_ = lean_box(0);
v_nameStx_x3f_1169_ = v___x_1192_;
v___y_1170_ = v_a_617_;
v___y_1171_ = v_a_618_;
goto v___jp_1168_;
}
v___jp_697_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_inc_ref_n(v___y_717_, 3);
v___x_724_ = l_Array_append___redArg(v___y_717_, v___y_723_);
lean_dec_ref(v___y_723_);
lean_inc_n(v___y_699_, 6);
lean_inc_n(v___y_715_, 18);
v___x_725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_725_, 0, v___y_715_);
lean_ctor_set(v___x_725_, 1, v___y_699_);
lean_ctor_set(v___x_725_, 2, v___x_724_);
v___x_726_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15));
lean_inc_ref(v___y_711_);
lean_inc_ref_n(v___y_718_, 6);
lean_inc_ref_n(v___y_706_, 7);
v___x_727_ = l_Lean_Name_mkStr4(v___y_706_, v___y_718_, v___y_711_, v___x_726_);
v___x_728_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16));
v___x_729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_729_, 0, v___y_715_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
lean_inc_ref(v___y_719_);
v___x_730_ = l_Lean_Syntax_SepArray_ofElems(v___y_719_, v___y_713_);
lean_dec_ref(v___y_713_);
v___x_731_ = l_Array_append___redArg(v___y_717_, v___x_730_);
lean_dec_ref(v___x_730_);
v___x_732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_732_, 0, v___y_715_);
lean_ctor_set(v___x_732_, 1, v___y_699_);
lean_ctor_set(v___x_732_, 2, v___x_731_);
v___x_733_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17));
v___x_734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_734_, 0, v___y_715_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
lean_inc(v___x_727_);
v___x_735_ = l_Lean_Syntax_node3(v___y_715_, v___x_727_, v___x_729_, v___x_732_, v___x_734_);
v___x_736_ = l_Lean_Syntax_node1(v___y_715_, v___y_699_, v___x_735_);
v___x_737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_737_, 0, v___y_715_);
lean_ctor_set(v___x_737_, 1, v___y_699_);
lean_ctor_set(v___x_737_, 2, v___y_717_);
lean_inc_ref_n(v___x_737_, 8);
lean_inc(v___y_716_);
v___x_738_ = l_Lean_Syntax_node7(v___y_715_, v___y_716_, v___x_725_, v___x_736_, v___x_737_, v___x_737_, v___x_737_, v___x_737_, v___x_737_);
v___x_739_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18));
lean_inc_ref_n(v___y_701_, 3);
v___x_740_ = l_Lean_Name_mkStr4(v___y_706_, v___y_718_, v___y_701_, v___x_739_);
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v___y_715_);
lean_ctor_set(v___x_741_, 1, v___x_739_);
v___x_742_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_743_ = l_Lean_Name_mkStr4(v___y_706_, v___y_718_, v___y_701_, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
lean_inc_n(v___y_712_, 2);
v___x_745_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_745_, 0, v___y_712_);
lean_ctor_set(v___x_745_, 1, v___y_699_);
lean_ctor_set(v___x_745_, 2, v___x_744_);
v___x_746_ = lean_mk_empty_array_with_capacity(v___x_696_);
lean_inc(v___y_705_);
lean_inc_ref(v___x_746_);
v___x_747_ = lean_array_push(v___x_746_, v___y_705_);
lean_inc_ref(v___x_745_);
v___x_748_ = lean_array_push(v___x_747_, v___x_745_);
lean_inc(v___x_743_);
v___x_749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_749_, 0, v___y_712_);
lean_ctor_set(v___x_749_, 1, v___x_743_);
lean_ctor_set(v___x_749_, 2, v___x_748_);
v___x_750_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_751_ = l_Lean_Name_mkStr4(v___y_706_, v___y_718_, v___y_701_, v___x_750_);
v___x_752_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_753_ = l_Lean_Name_mkStr4(v___y_706_, v___y_718_, v___y_711_, v___x_752_);
v___x_754_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_755_, 0, v___y_715_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20);
v___x_757_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21));
v___x_758_ = l_Lean_addMacroScope(v___y_704_, v___x_757_, v___y_698_);
v___x_759_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23));
v___x_760_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24));
lean_inc(v___y_702_);
v___x_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v___y_702_);
v___x_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_759_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_763_, 0, v___y_715_);
lean_ctor_set(v___x_763_, 1, v___x_756_);
lean_ctor_set(v___x_763_, 2, v___x_758_);
lean_ctor_set(v___x_763_, 3, v___x_762_);
v___x_764_ = l_Lean_Syntax_node2(v___y_715_, v___x_753_, v___x_755_, v___x_763_);
v___x_765_ = l_Lean_Syntax_node1(v___y_715_, v___y_699_, v___x_764_);
lean_inc(v___x_751_);
v___x_766_ = l_Lean_Syntax_node2(v___y_715_, v___x_751_, v___x_737_, v___x_765_);
v___x_767_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25));
v___x_768_ = l_Lean_Name_mkStr4(v___y_706_, v___y_718_, v___y_701_, v___x_767_);
lean_inc_ref(v___y_707_);
v___x_769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_769_, 0, v___y_715_);
lean_ctor_set(v___x_769_, 1, v___y_707_);
v___x_770_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26));
v___x_771_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27));
v___x_772_ = l_Lean_Name_mkStr4(v___y_706_, v___y_718_, v___x_770_, v___x_771_);
lean_inc(v___x_772_);
v___x_773_ = l_Lean_Syntax_node2(v___y_715_, v___x_772_, v___x_737_, v___x_737_);
lean_inc(v___x_768_);
v___x_774_ = l_Lean_Syntax_node4(v___y_715_, v___x_768_, v___x_769_, v___y_709_, v___x_773_, v___x_737_);
lean_inc(v___x_740_);
v___x_775_ = l_Lean_Syntax_node4(v___y_715_, v___x_740_, v___x_741_, v___x_749_, v___x_766_, v___x_774_);
lean_inc(v___y_708_);
v___x_776_ = l_Lean_Syntax_node2(v___y_715_, v___y_708_, v___x_738_, v___x_775_);
lean_inc(v___x_776_);
v___x_777_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_777_, 0, v___x_776_);
v___x_778_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_stx_616_, v___x_776_, v___x_777_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v___x_779_; 
lean_dec_ref_known(v___x_778_, 1);
v___x_779_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_781_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref_known(v___x_779_, 1);
v___x_781_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_720_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref_known(v___x_781_, 1);
v___x_782_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___x_783_ = l_Lean_Name_str___override(v___y_703_, v___x_782_);
v___x_784_ = l_Lean_mkIdentFrom(v___y_705_, v___x_783_, v___y_700_);
lean_dec(v___y_705_);
if (lean_obj_tag(v___y_710_) == 0)
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_721_);
lean_dec_ref(v___x_785_);
v___y_621_ = v___y_699_;
v___y_622_ = v___x_746_;
v___y_623_ = v___y_712_;
v___y_624_ = v___x_733_;
v___y_625_ = v___y_714_;
v___y_626_ = v___x_768_;
v___y_627_ = v_a_780_;
v___y_628_ = v___x_772_;
v___y_629_ = v___y_716_;
v___y_630_ = v___x_784_;
v___y_631_ = v___x_745_;
v___y_632_ = v___y_717_;
v___y_633_ = v___y_706_;
v___y_634_ = v___x_727_;
v___y_635_ = v___y_707_;
v___y_636_ = v___y_720_;
v___y_637_ = v___y_708_;
v___y_638_ = v___x_739_;
v___y_639_ = v___y_721_;
v___y_640_ = v___x_740_;
v___y_641_ = v___y_722_;
v___y_642_ = v___x_751_;
v___y_643_ = v___x_743_;
v___y_644_ = v___x_728_;
goto v___jp_620_;
}
else
{
lean_dec_ref_known(v___y_710_, 1);
v___y_621_ = v___y_699_;
v___y_622_ = v___x_746_;
v___y_623_ = v___y_712_;
v___y_624_ = v___x_733_;
v___y_625_ = v___y_714_;
v___y_626_ = v___x_768_;
v___y_627_ = v_a_780_;
v___y_628_ = v___x_772_;
v___y_629_ = v___y_716_;
v___y_630_ = v___x_784_;
v___y_631_ = v___x_745_;
v___y_632_ = v___y_717_;
v___y_633_ = v___y_706_;
v___y_634_ = v___x_727_;
v___y_635_ = v___y_707_;
v___y_636_ = v___y_720_;
v___y_637_ = v___y_708_;
v___y_638_ = v___x_739_;
v___y_639_ = v___y_721_;
v___y_640_ = v___x_740_;
v___y_641_ = v___y_722_;
v___y_642_ = v___x_751_;
v___y_643_ = v___x_743_;
v___y_644_ = v___x_728_;
goto v___jp_620_;
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v_a_780_);
lean_dec(v___x_772_);
lean_dec(v___x_768_);
lean_dec(v___x_751_);
lean_dec_ref(v___x_746_);
lean_dec_ref_known(v___x_745_, 3);
lean_dec(v___x_743_);
lean_dec(v___x_740_);
lean_dec(v___x_727_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_716_);
lean_dec(v___y_714_);
lean_dec(v___y_712_);
lean_dec(v___y_710_);
lean_dec(v___y_708_);
lean_dec(v___y_705_);
lean_dec(v___y_703_);
v_a_786_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_781_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_781_);
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
lean_dec(v___x_772_);
lean_dec(v___x_768_);
lean_dec(v___x_751_);
lean_dec_ref(v___x_746_);
lean_dec_ref_known(v___x_745_, 3);
lean_dec(v___x_743_);
lean_dec(v___x_740_);
lean_dec(v___x_727_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_716_);
lean_dec(v___y_714_);
lean_dec(v___y_712_);
lean_dec(v___y_710_);
lean_dec(v___y_708_);
lean_dec(v___y_705_);
lean_dec(v___y_703_);
v_a_794_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_779_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_779_);
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
lean_dec(v___x_772_);
lean_dec(v___x_768_);
lean_dec(v___x_751_);
lean_dec_ref(v___x_746_);
lean_dec_ref_known(v___x_745_, 3);
lean_dec(v___x_743_);
lean_dec(v___x_740_);
lean_dec(v___x_727_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_716_);
lean_dec(v___y_714_);
lean_dec(v___y_712_);
lean_dec(v___y_710_);
lean_dec(v___y_708_);
lean_dec(v___y_705_);
lean_dec(v___y_703_);
return v___x_778_;
}
}
v___jp_802_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_826_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_827_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_818_, 2);
lean_inc_ref_n(v___y_817_, 2);
v___x_828_ = l_Lean_Name_mkStr4(v___y_817_, v___y_818_, v___x_826_, v___x_827_);
v___x_829_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_830_ = l_Lean_Name_mkStr4(v___y_817_, v___y_818_, v___x_826_, v___x_829_);
if (lean_obj_tag(v___y_822_) == 1)
{
lean_object* v_val_831_; lean_object* v___x_832_; 
v_val_831_ = lean_ctor_get(v___y_822_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v___y_822_, 1);
v___x_832_ = l_Array_mkArray1___redArg(v_val_831_);
v___y_698_ = v___y_803_;
v___y_699_ = v___y_804_;
v___y_700_ = v___y_808_;
v___y_701_ = v___x_826_;
v___y_702_ = v___y_813_;
v___y_703_ = v___y_814_;
v___y_704_ = v_a_825_;
v___y_705_ = v___y_815_;
v___y_706_ = v___y_817_;
v___y_707_ = v___y_819_;
v___y_708_ = v___x_828_;
v___y_709_ = v___y_805_;
v___y_710_ = v___y_806_;
v___y_711_ = v___y_807_;
v___y_712_ = v___y_809_;
v___y_713_ = v___y_811_;
v___y_714_ = v___y_810_;
v___y_715_ = v___y_812_;
v___y_716_ = v___x_830_;
v___y_717_ = v___y_816_;
v___y_718_ = v___y_818_;
v___y_719_ = v___y_821_;
v___y_720_ = v___y_820_;
v___y_721_ = v___y_823_;
v___y_722_ = v___y_824_;
v___y_723_ = v___x_832_;
goto v___jp_697_;
}
else
{
lean_object* v___x_833_; 
lean_dec(v___y_822_);
v___x_833_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
v___y_698_ = v___y_803_;
v___y_699_ = v___y_804_;
v___y_700_ = v___y_808_;
v___y_701_ = v___x_826_;
v___y_702_ = v___y_813_;
v___y_703_ = v___y_814_;
v___y_704_ = v_a_825_;
v___y_705_ = v___y_815_;
v___y_706_ = v___y_817_;
v___y_707_ = v___y_819_;
v___y_708_ = v___x_828_;
v___y_709_ = v___y_805_;
v___y_710_ = v___y_806_;
v___y_711_ = v___y_807_;
v___y_712_ = v___y_809_;
v___y_713_ = v___y_811_;
v___y_714_ = v___y_810_;
v___y_715_ = v___y_812_;
v___y_716_ = v___x_830_;
v___y_717_ = v___y_816_;
v___y_718_ = v___y_818_;
v___y_719_ = v___y_821_;
v___y_720_ = v___y_820_;
v___y_721_ = v___y_823_;
v___y_722_ = v___y_824_;
v___y_723_ = v___x_833_;
goto v___jp_697_;
}
}
v___jp_834_:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_859_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
lean_inc_ref_n(v___y_837_, 6);
lean_inc_ref_n(v___y_851_, 6);
lean_inc_ref_n(v___y_850_, 6);
v___x_860_ = l_Lean_Name_mkStr4(v___y_850_, v___y_851_, v___y_837_, v___x_859_);
v___x_861_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31));
lean_inc_n(v___y_841_, 28);
v___x_862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_862_, 0, v___y_841_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
lean_inc_ref(v___y_848_);
lean_inc_n(v___y_835_, 6);
v___x_863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_863_, 0, v___y_841_);
lean_ctor_set(v___x_863_, 1, v___y_835_);
lean_ctor_set(v___x_863_, 2, v___y_848_);
v___x_864_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31));
v___x_865_ = l_Lean_Name_mkStr4(v___y_850_, v___y_851_, v___y_837_, v___x_864_);
v___x_866_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32));
v___x_867_ = l_Lean_Name_mkStr4(v___y_850_, v___y_851_, v___y_837_, v___x_866_);
v___x_868_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33));
v___x_869_ = l_Lean_Name_mkStr4(v___y_850_, v___y_851_, v___y_837_, v___x_868_);
v___x_870_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35);
v___x_871_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36));
lean_inc_n(v___y_852_, 3);
lean_inc_n(v_a_858_, 3);
v___x_872_ = l_Lean_addMacroScope(v_a_858_, v___x_871_, v___y_852_);
lean_inc_n(v___y_846_, 4);
v___x_873_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_873_, 0, v___y_841_);
lean_ctor_set(v___x_873_, 1, v___x_870_);
lean_ctor_set(v___x_873_, 2, v___x_872_);
lean_ctor_set(v___x_873_, 3, v___y_846_);
lean_inc_ref_n(v___x_863_, 18);
lean_inc_n(v___x_869_, 3);
v___x_874_ = l_Lean_Syntax_node2(v___y_841_, v___x_869_, v___x_873_, v___x_863_);
v___x_875_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37));
v___x_876_ = l_Lean_Name_mkStr4(v___y_850_, v___y_851_, v___y_837_, v___x_875_);
v___x_877_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38));
v___x_878_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_878_, 0, v___y_841_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
lean_inc_ref_n(v___x_878_, 3);
lean_inc_n(v___x_876_, 3);
v___x_879_ = l_Lean_Syntax_node3(v___y_841_, v___x_876_, v___x_878_, v___x_863_, v___y_840_);
v___x_880_ = l_Lean_Syntax_node3(v___y_841_, v___y_835_, v___x_863_, v___x_863_, v___x_879_);
lean_inc_n(v___x_867_, 3);
v___x_881_ = l_Lean_Syntax_node2(v___y_841_, v___x_867_, v___x_874_, v___x_880_);
v___x_882_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39));
v___x_883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_883_, 0, v___y_841_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41);
v___x_885_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42));
v___x_886_ = l_Lean_addMacroScope(v_a_858_, v___x_885_, v___y_852_);
v___x_887_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_887_, 0, v___y_841_);
lean_ctor_set(v___x_887_, 1, v___x_884_);
lean_ctor_set(v___x_887_, 2, v___x_886_);
lean_ctor_set(v___x_887_, 3, v___y_846_);
v___x_888_ = l_Lean_Syntax_node2(v___y_841_, v___x_869_, v___x_887_, v___x_863_);
v___x_889_ = l_Lean_Syntax_node3(v___y_841_, v___x_876_, v___x_878_, v___x_863_, v___y_838_);
v___x_890_ = l_Lean_Syntax_node3(v___y_841_, v___y_835_, v___x_863_, v___x_863_, v___x_889_);
v___x_891_ = l_Lean_Syntax_node2(v___y_841_, v___x_867_, v___x_888_, v___x_890_);
v___x_892_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44);
v___x_893_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45));
v___x_894_ = l_Lean_addMacroScope(v_a_858_, v___x_893_, v___y_852_);
v___x_895_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_895_, 0, v___y_841_);
lean_ctor_set(v___x_895_, 1, v___x_892_);
lean_ctor_set(v___x_895_, 2, v___x_894_);
lean_ctor_set(v___x_895_, 3, v___y_846_);
v___x_896_ = l_Lean_Syntax_node2(v___y_841_, v___x_869_, v___x_895_, v___x_863_);
v___x_897_ = l_Lean_Syntax_node3(v___y_841_, v___x_876_, v___x_878_, v___x_863_, v___y_855_);
v___x_898_ = l_Lean_Syntax_node3(v___y_841_, v___y_835_, v___x_863_, v___x_863_, v___x_897_);
v___x_899_ = l_Lean_Syntax_node2(v___y_841_, v___x_867_, v___x_896_, v___x_898_);
v___x_900_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47);
v___x_901_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48));
v___x_902_ = l_Lean_addMacroScope(v_a_858_, v___x_901_, v___y_852_);
v___x_903_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_903_, 0, v___y_841_);
lean_ctor_set(v___x_903_, 1, v___x_900_);
lean_ctor_set(v___x_903_, 2, v___x_902_);
lean_ctor_set(v___x_903_, 3, v___y_846_);
v___x_904_ = l_Lean_Syntax_node2(v___y_841_, v___x_869_, v___x_903_, v___x_863_);
v___x_905_ = l_Lean_Syntax_node3(v___y_841_, v___x_876_, v___x_878_, v___x_863_, v___y_849_);
v___x_906_ = l_Lean_Syntax_node3(v___y_841_, v___y_835_, v___x_863_, v___x_863_, v___x_905_);
v___x_907_ = l_Lean_Syntax_node2(v___y_841_, v___x_867_, v___x_904_, v___x_906_);
lean_inc_ref_n(v___x_883_, 2);
v___x_908_ = l_Lean_Syntax_node7(v___y_841_, v___y_835_, v___x_881_, v___x_883_, v___x_891_, v___x_883_, v___x_899_, v___x_883_, v___x_907_);
v___x_909_ = l_Lean_Syntax_node1(v___y_841_, v___x_865_, v___x_908_);
v___x_910_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49));
v___x_911_ = l_Lean_Name_mkStr4(v___y_850_, v___y_851_, v___y_837_, v___x_910_);
v___x_912_ = l_Lean_Syntax_node1(v___y_841_, v___x_911_, v___x_863_);
v___x_913_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50));
v___x_914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_914_, 0, v___y_841_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = l_Lean_Syntax_node6(v___y_841_, v___x_860_, v___x_862_, v___x_863_, v___x_909_, v___x_912_, v___x_863_, v___x_914_);
v___x_916_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_853_, v___y_856_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_853_);
if (lean_obj_tag(v___x_918_) == 0)
{
if (lean_obj_tag(v___y_836_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_920_; lean_object* v_a_921_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_918_, 1);
v___x_920_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_856_);
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref(v___x_920_);
v___y_803_ = v_a_919_;
v___y_804_ = v___y_835_;
v___y_805_ = v___x_915_;
v___y_806_ = v___y_836_;
v___y_807_ = v___y_837_;
v___y_808_ = v___y_839_;
v___y_809_ = v___y_842_;
v___y_810_ = v___y_844_;
v___y_811_ = v___y_843_;
v___y_812_ = v_a_917_;
v___y_813_ = v___y_846_;
v___y_814_ = v___y_845_;
v___y_815_ = v___y_847_;
v___y_816_ = v___y_848_;
v___y_817_ = v___y_850_;
v___y_818_ = v___y_851_;
v___y_819_ = v___x_877_;
v___y_820_ = v___y_853_;
v___y_821_ = v___x_882_;
v___y_822_ = v___y_854_;
v___y_823_ = v___y_856_;
v___y_824_ = v___y_857_;
v_a_825_ = v_a_921_;
goto v___jp_802_;
}
else
{
lean_object* v_a_922_; lean_object* v_val_923_; 
v_a_922_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_918_, 1);
v_val_923_ = lean_ctor_get(v___y_836_, 0);
lean_inc(v_val_923_);
v___y_803_ = v_a_922_;
v___y_804_ = v___y_835_;
v___y_805_ = v___x_915_;
v___y_806_ = v___y_836_;
v___y_807_ = v___y_837_;
v___y_808_ = v___y_839_;
v___y_809_ = v___y_842_;
v___y_810_ = v___y_844_;
v___y_811_ = v___y_843_;
v___y_812_ = v_a_917_;
v___y_813_ = v___y_846_;
v___y_814_ = v___y_845_;
v___y_815_ = v___y_847_;
v___y_816_ = v___y_848_;
v___y_817_ = v___y_850_;
v___y_818_ = v___y_851_;
v___y_819_ = v___x_877_;
v___y_820_ = v___y_853_;
v___y_821_ = v___x_882_;
v___y_822_ = v___y_854_;
v___y_823_ = v___y_856_;
v___y_824_ = v___y_857_;
v_a_825_ = v_val_923_;
goto v___jp_802_;
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_a_917_);
lean_dec(v___x_915_);
lean_dec(v___y_857_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_847_);
lean_dec(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec(v_stx_616_);
v_a_924_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_918_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_918_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec(v___x_915_);
lean_dec(v___y_857_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_847_);
lean_dec(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec(v_stx_616_);
v_a_932_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_916_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_916_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
v___jp_940_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_958_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_959_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_960_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51));
lean_inc_ref_n(v___y_950_, 2);
v___x_961_ = l_Lean_Name_mkStr4(v___y_950_, v___x_958_, v___x_959_, v___x_960_);
v___x_962_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52));
v___x_963_ = l_Lean_Name_mkStr4(v___y_950_, v___x_958_, v___x_959_, v___x_962_);
v___x_964_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_965_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___y_956_, 2);
v___x_966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_966_, 0, v___y_956_);
lean_ctor_set(v___x_966_, 1, v___x_964_);
lean_ctor_set(v___x_966_, 2, v___x_965_);
lean_inc_ref(v___x_966_);
lean_inc(v___x_963_);
v___x_967_ = l_Lean_Syntax_node1(v___y_956_, v___x_963_, v___x_966_);
v___x_968_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_951_, v___y_955_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_951_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v___x_970_, 1);
v___x_972_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54);
v___x_973_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56));
v___x_974_ = l_Lean_addMacroScope(v_a_957_, v___x_973_, v___y_947_);
lean_inc(v___y_948_);
lean_inc_n(v___y_956_, 2);
v___x_975_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_975_, 0, v___y_956_);
lean_ctor_set(v___x_975_, 1, v___x_972_);
lean_ctor_set(v___x_975_, 2, v___x_974_);
lean_ctor_set(v___x_975_, 3, v___y_948_);
v___x_976_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57));
v___x_977_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58));
lean_inc_ref(v___y_950_);
v___x_978_ = l_Lean_Name_mkStr4(v___y_950_, v___x_958_, v___x_976_, v___x_977_);
v___x_979_ = l_Lean_Syntax_node2(v___y_956_, v___x_978_, v___x_975_, v___x_966_);
lean_inc(v___x_961_);
v___x_980_ = l_Lean_Syntax_node2(v___y_956_, v___x_961_, v___x_967_, v___x_979_);
v___x_981_ = lean_mk_empty_array_with_capacity(v___x_694_);
v___x_982_ = lean_array_push(v___x_981_, v___x_980_);
v___x_983_ = l_Lake_DSL_expandAttrs(v___y_954_);
v___x_984_ = l_Array_append___redArg(v___x_982_, v___x_983_);
lean_dec_ref(v___x_983_);
v___x_985_ = l_Lake_DSL_packageDeclName;
v___x_986_ = l_Lean_mkIdentFrom(v___y_946_, v___x_985_, v___y_943_);
lean_dec(v___y_946_);
if (lean_obj_tag(v___y_941_) == 0)
{
lean_object* v___x_987_; lean_object* v_a_988_; 
v___x_987_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_955_);
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref(v___x_987_);
v___y_835_ = v___x_964_;
v___y_836_ = v___y_941_;
v___y_837_ = v___x_959_;
v___y_838_ = v___y_942_;
v___y_839_ = v___y_943_;
v___y_840_ = v___y_944_;
v___y_841_ = v_a_969_;
v___y_842_ = v___y_945_;
v___y_843_ = v___x_984_;
v___y_844_ = v___x_963_;
v___y_845_ = v___x_985_;
v___y_846_ = v___y_948_;
v___y_847_ = v___x_986_;
v___y_848_ = v___x_965_;
v___y_849_ = v___y_949_;
v___y_850_ = v___y_950_;
v___y_851_ = v___x_958_;
v___y_852_ = v_a_971_;
v___y_853_ = v___y_951_;
v___y_854_ = v___y_952_;
v___y_855_ = v___y_953_;
v___y_856_ = v___y_955_;
v___y_857_ = v___x_961_;
v_a_858_ = v_a_988_;
goto v___jp_834_;
}
else
{
lean_object* v_val_989_; 
v_val_989_ = lean_ctor_get(v___y_941_, 0);
lean_inc(v_val_989_);
v___y_835_ = v___x_964_;
v___y_836_ = v___y_941_;
v___y_837_ = v___x_959_;
v___y_838_ = v___y_942_;
v___y_839_ = v___y_943_;
v___y_840_ = v___y_944_;
v___y_841_ = v_a_969_;
v___y_842_ = v___y_945_;
v___y_843_ = v___x_984_;
v___y_844_ = v___x_963_;
v___y_845_ = v___x_985_;
v___y_846_ = v___y_948_;
v___y_847_ = v___x_986_;
v___y_848_ = v___x_965_;
v___y_849_ = v___y_949_;
v___y_850_ = v___y_950_;
v___y_851_ = v___x_958_;
v___y_852_ = v_a_971_;
v___y_853_ = v___y_951_;
v___y_854_ = v___y_952_;
v___y_855_ = v___y_953_;
v___y_856_ = v___y_955_;
v___y_857_ = v___x_961_;
v_a_858_ = v_val_989_;
goto v___jp_834_;
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_a_969_);
lean_dec(v___x_967_);
lean_dec_ref_known(v___x_966_, 3);
lean_dec(v___x_963_);
lean_dec(v___x_961_);
lean_dec(v_a_957_);
lean_dec(v___y_956_);
lean_dec(v___y_954_);
lean_dec(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_949_);
lean_dec(v___y_947_);
lean_dec(v___y_946_);
lean_dec(v___y_945_);
lean_dec(v___y_944_);
lean_dec(v___y_942_);
lean_dec(v___y_941_);
lean_dec(v_stx_616_);
v_a_990_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_970_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_970_);
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
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v___x_967_);
lean_dec_ref_known(v___x_966_, 3);
lean_dec(v___x_963_);
lean_dec(v___x_961_);
lean_dec(v_a_957_);
lean_dec(v___y_956_);
lean_dec(v___y_954_);
lean_dec(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_949_);
lean_dec(v___y_947_);
lean_dec(v___y_946_);
lean_dec(v___y_945_);
lean_dec(v___y_944_);
lean_dec(v___y_942_);
lean_dec(v___y_941_);
lean_dec(v_stx_616_);
v_a_998_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_968_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_968_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
v___jp_1006_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1020_ = l_Nat_reprFast(v___y_1013_);
v___x_1021_ = lean_box(2);
v___x_1022_ = l_Lean_Syntax_mkNumLit(v___x_1020_, v___x_1021_);
v___x_1023_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1024_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61));
v___x_1025_ = lean_mk_empty_array_with_capacity(v___x_696_);
lean_inc(v___y_1019_);
lean_inc_ref(v___x_1025_);
v___x_1026_ = lean_array_push(v___x_1025_, v___y_1019_);
v___x_1027_ = lean_array_push(v___x_1026_, v___x_1022_);
v___x_1028_ = l_Lean_Syntax_mkCApp(v___x_1024_, v___x_1027_);
v___x_1029_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63));
lean_inc(v___x_1028_);
v___x_1030_ = lean_array_push(v___x_1025_, v___x_1028_);
lean_inc(v___y_1007_);
v___x_1031_ = lean_array_push(v___x_1030_, v___y_1007_);
v___x_1032_ = l_Lean_Syntax_mkCApp(v___x_1029_, v___x_1031_);
lean_inc(v___y_1012_);
v___x_1033_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v___x_1029_, v___y_1012_, v___x_1032_, v___y_1014_, v___y_1015_, v___y_1018_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v___x_1034_; 
lean_dec_ref_known(v___x_1033_, 1);
v___x_1034_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_1015_, v___y_1018_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1015_);
if (lean_obj_tag(v___x_1036_) == 0)
{
if (lean_obj_tag(v___y_1008_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v_a_1039_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1038_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1018_);
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref(v___x_1038_);
v___y_941_ = v___y_1008_;
v___y_942_ = v___y_1007_;
v___y_943_ = v___y_1009_;
v___y_944_ = v___y_1019_;
v___y_945_ = v___x_1021_;
v___y_946_ = v___y_1010_;
v___y_947_ = v_a_1037_;
v___y_948_ = v___y_1011_;
v___y_949_ = v___y_1012_;
v___y_950_ = v___x_1023_;
v___y_951_ = v___y_1015_;
v___y_952_ = v___y_1016_;
v___y_953_ = v___x_1028_;
v___y_954_ = v___y_1017_;
v___y_955_ = v___y_1018_;
v___y_956_ = v_a_1035_;
v_a_957_ = v_a_1039_;
goto v___jp_940_;
}
else
{
lean_object* v_a_1040_; lean_object* v_val_1041_; 
v_a_1040_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1036_, 1);
v_val_1041_ = lean_ctor_get(v___y_1008_, 0);
lean_inc(v_val_1041_);
v___y_941_ = v___y_1008_;
v___y_942_ = v___y_1007_;
v___y_943_ = v___y_1009_;
v___y_944_ = v___y_1019_;
v___y_945_ = v___x_1021_;
v___y_946_ = v___y_1010_;
v___y_947_ = v_a_1040_;
v___y_948_ = v___y_1011_;
v___y_949_ = v___y_1012_;
v___y_950_ = v___x_1023_;
v___y_951_ = v___y_1015_;
v___y_952_ = v___y_1016_;
v___y_953_ = v___x_1028_;
v___y_954_ = v___y_1017_;
v___y_955_ = v___y_1018_;
v___y_956_ = v_a_1035_;
v_a_957_ = v_val_1041_;
goto v___jp_940_;
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_a_1035_);
lean_dec(v___x_1028_);
lean_dec(v___y_1019_);
lean_dec(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1012_);
lean_dec(v___y_1010_);
lean_dec(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec(v_stx_616_);
v_a_1042_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1036_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1036_);
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
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v___x_1028_);
lean_dec(v___y_1019_);
lean_dec(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1012_);
lean_dec(v___y_1010_);
lean_dec(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec(v_stx_616_);
v_a_1050_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1034_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1034_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_dec(v___x_1028_);
lean_dec(v___y_1019_);
lean_dec(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1012_);
lean_dec(v___y_1010_);
lean_dec(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec(v_stx_616_);
return v___x_1033_;
}
}
v___jp_1058_:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lake_DSL_mkConfigDeclIdent(v___y_1061_, v___y_1063_, v___y_1066_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; lean_object* v_env_1073_; lean_object* v___x_1074_; lean_object* v_asyncMode_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v_fst_1079_; lean_object* v_snd_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc_n(v_a_1071_, 2);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1072_ = lean_st_ref_get(v___y_1066_);
v_env_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc_ref(v_env_1073_);
lean_dec(v___x_1072_);
v___x_1074_ = l_Lake_nameExt;
v_asyncMode_1075_ = lean_ctor_get(v___x_1074_, 2);
v___x_1076_ = lean_box(0);
v___x_1077_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64));
v___x_1078_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1077_, v___x_1074_, v_env_1073_, v_asyncMode_1075_, v___x_1076_);
v_fst_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_fst_1079_);
v_snd_1080_ = lean_ctor_get(v___x_1078_, 1);
lean_inc(v_snd_1080_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66);
v___x_1082_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67));
v___x_1083_ = l_Lean_addMacroScope(v_a_1069_, v___x_1082_, v___y_1067_);
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1085_, 0, v___y_1068_);
lean_ctor_set(v___x_1085_, 1, v___x_1081_);
lean_ctor_set(v___x_1085_, 2, v___x_1083_);
lean_ctor_set(v___x_1085_, 3, v___x_1084_);
v___x_1086_ = l_Lean_TSyntax_getId(v_a_1071_);
v___x_1087_ = l_Lake_Name_quoteFrom(v_a_1071_, v___x_1086_, v___y_1060_);
if (lean_obj_tag(v_snd_1080_) == 0)
{
lean_inc(v___x_1087_);
v___y_1007_ = v___x_1087_;
v___y_1008_ = v___y_1059_;
v___y_1009_ = v___y_1060_;
v___y_1010_ = v_a_1071_;
v___y_1011_ = v___x_1084_;
v___y_1012_ = v___x_1085_;
v___y_1013_ = v_fst_1079_;
v___y_1014_ = v___y_1062_;
v___y_1015_ = v___y_1063_;
v___y_1016_ = v___y_1064_;
v___y_1017_ = v___y_1065_;
v___y_1018_ = v___y_1066_;
v___y_1019_ = v___x_1087_;
goto v___jp_1006_;
}
else
{
lean_object* v___x_1088_; 
lean_inc(v_a_1071_);
v___x_1088_ = l_Lake_Name_quoteFrom(v_a_1071_, v_snd_1080_, v___y_1060_);
v___y_1007_ = v___x_1087_;
v___y_1008_ = v___y_1059_;
v___y_1009_ = v___y_1060_;
v___y_1010_ = v_a_1071_;
v___y_1011_ = v___x_1084_;
v___y_1012_ = v___x_1085_;
v___y_1013_ = v_fst_1079_;
v___y_1014_ = v___y_1062_;
v___y_1015_ = v___y_1063_;
v___y_1016_ = v___y_1064_;
v___y_1017_ = v___y_1065_;
v___y_1018_ = v___y_1066_;
v___y_1019_ = v___x_1088_;
goto v___jp_1006_;
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v_a_1069_);
lean_dec(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec(v___y_1059_);
lean_dec(v_stx_616_);
v_a_1089_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1070_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1070_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
v___jp_1098_:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_Elab_Command_getRef___redArg(v___y_1099_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v_fileName_1107_; lean_object* v_fileMap_1108_; lean_object* v_currRecDepth_1109_; lean_object* v_cmdPos_1110_; lean_object* v_macroStack_1111_; lean_object* v_quotContext_x3f_1112_; lean_object* v_currMacroScope_1113_; lean_object* v_snap_x3f_1114_; lean_object* v_cancelTk_x3f_1115_; uint8_t v_suppressElabErrors_1116_; lean_object* v_ref_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v_fileName_1107_ = lean_ctor_get(v___y_1099_, 0);
v_fileMap_1108_ = lean_ctor_get(v___y_1099_, 1);
v_currRecDepth_1109_ = lean_ctor_get(v___y_1099_, 2);
v_cmdPos_1110_ = lean_ctor_get(v___y_1099_, 3);
v_macroStack_1111_ = lean_ctor_get(v___y_1099_, 4);
v_quotContext_x3f_1112_ = lean_ctor_get(v___y_1099_, 5);
v_currMacroScope_1113_ = lean_ctor_get(v___y_1099_, 6);
v_snap_x3f_1114_ = lean_ctor_get(v___y_1099_, 8);
v_cancelTk_x3f_1115_ = lean_ctor_get(v___y_1099_, 9);
v_suppressElabErrors_1116_ = lean_ctor_get_uint8(v___y_1099_, sizeof(void*)*10);
v_ref_1117_ = l_Lean_replaceRef(v_kw_1097_, v_a_1106_);
lean_dec(v_a_1106_);
lean_dec(v_kw_1097_);
lean_inc(v_cancelTk_x3f_1115_);
lean_inc(v_snap_x3f_1114_);
lean_inc(v_currMacroScope_1113_);
lean_inc(v_quotContext_x3f_1112_);
lean_inc(v_macroStack_1111_);
lean_inc(v_cmdPos_1110_);
lean_inc(v_currRecDepth_1109_);
lean_inc_ref(v_fileMap_1108_);
lean_inc_ref(v_fileName_1107_);
v___x_1118_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1118_, 0, v_fileName_1107_);
lean_ctor_set(v___x_1118_, 1, v_fileMap_1108_);
lean_ctor_set(v___x_1118_, 2, v_currRecDepth_1109_);
lean_ctor_set(v___x_1118_, 3, v_cmdPos_1110_);
lean_ctor_set(v___x_1118_, 4, v_macroStack_1111_);
lean_ctor_set(v___x_1118_, 5, v_quotContext_x3f_1112_);
lean_ctor_set(v___x_1118_, 6, v_currMacroScope_1113_);
lean_ctor_set(v___x_1118_, 7, v_ref_1117_);
lean_ctor_set(v___x_1118_, 8, v_snap_x3f_1114_);
lean_ctor_set(v___x_1118_, 9, v_cancelTk_x3f_1115_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*10, v_suppressElabErrors_1116_);
v___x_1119_ = l_Lean_Elab_Command_getRef___redArg(v___x_1118_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1118_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1123_ = 0;
v___x_1124_ = l_Lean_SourceInfo_fromRef(v_a_1120_, v___x_1123_);
lean_dec(v_a_1120_);
if (lean_obj_tag(v_quotContext_x3f_1112_) == 0)
{
lean_object* v___x_1125_; lean_object* v_a_1126_; 
v___x_1125_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1103_);
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref(v___x_1125_);
v___y_1059_ = v_quotContext_x3f_1112_;
v___y_1060_ = v___x_1123_;
v___y_1061_ = v___y_1100_;
v___y_1062_ = v___y_1101_;
v___y_1063_ = v___x_1118_;
v___y_1064_ = v___y_1104_;
v___y_1065_ = v___y_1102_;
v___y_1066_ = v___y_1103_;
v___y_1067_ = v_a_1122_;
v___y_1068_ = v___x_1124_;
v_a_1069_ = v_a_1126_;
goto v___jp_1058_;
}
else
{
lean_object* v_val_1127_; 
v_val_1127_ = lean_ctor_get(v_quotContext_x3f_1112_, 0);
lean_inc(v_val_1127_);
lean_inc_ref(v_quotContext_x3f_1112_);
v___y_1059_ = v_quotContext_x3f_1112_;
v___y_1060_ = v___x_1123_;
v___y_1061_ = v___y_1100_;
v___y_1062_ = v___y_1101_;
v___y_1063_ = v___x_1118_;
v___y_1064_ = v___y_1104_;
v___y_1065_ = v___y_1102_;
v___y_1066_ = v___y_1103_;
v___y_1067_ = v_a_1122_;
v___y_1068_ = v___x_1124_;
v_a_1069_ = v_val_1127_;
goto v___jp_1058_;
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v_a_1120_);
lean_dec_ref_known(v___x_1118_, 10);
lean_dec(v___y_1104_);
lean_dec(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec(v_stx_616_);
v_a_1128_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1121_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1121_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref_known(v___x_1118_, 10);
lean_dec(v___y_1104_);
lean_dec(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec(v_stx_616_);
v_a_1136_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1119_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1119_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v___y_1104_);
lean_dec(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec(v_kw_1097_);
lean_dec(v_stx_616_);
v_a_1144_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1105_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1105_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
v___jp_1152_:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Syntax_getOptional_x3f(v___x_693_);
lean_dec(v___x_693_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_box(0);
v___y_1099_ = v___y_1153_;
v___y_1100_ = v___y_1154_;
v___y_1101_ = v___y_1155_;
v___y_1102_ = v___y_1157_;
v___y_1103_ = v___y_1156_;
v___y_1104_ = v___x_1159_;
goto v___jp_1098_;
}
else
{
lean_object* v_val_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
v_val_1160_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1158_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_val_1160_);
lean_dec(v___x_1158_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_val_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
v___y_1099_ = v___y_1153_;
v___y_1100_ = v___y_1154_;
v___y_1101_ = v___y_1155_;
v___y_1102_ = v___y_1157_;
v___y_1103_ = v___y_1156_;
v___y_1104_ = v___x_1165_;
goto v___jp_1098_;
}
}
}
}
v___jp_1168_:
{
lean_object* v___x_1172_; lean_object* v_cfg_1173_; lean_object* v___x_1174_; 
v___x_1172_ = lean_unsigned_to_nat(4u);
v_cfg_1173_ = l_Lean_Syntax_getArg(v_stx_616_, v___x_1172_);
v___x_1174_ = l_Lean_Syntax_getOptional_x3f(v___x_695_);
lean_dec(v___x_695_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_box(0);
v___y_1153_ = v___y_1170_;
v___y_1154_ = v_nameStx_x3f_1169_;
v___y_1155_ = v_cfg_1173_;
v___y_1156_ = v___y_1171_;
v___y_1157_ = v___x_1175_;
goto v___jp_1152_;
}
else
{
lean_object* v_val_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
v_val_1176_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1174_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_val_1176_);
lean_dec(v___x_1174_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_val_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
v___y_1153_ = v___y_1170_;
v___y_1154_ = v_nameStx_x3f_1169_;
v___y_1155_ = v_cfg_1173_;
v___y_1156_ = v___y_1171_;
v___y_1157_ = v___x_1181_;
goto v___jp_1152_;
}
}
}
}
}
v___jp_620_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_inc_ref(v___y_632_);
lean_inc_n(v___y_621_, 5);
lean_inc_n(v___y_627_, 28);
v___x_645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_645_, 0, v___y_627_);
lean_ctor_set(v___x_645_, 1, v___y_621_);
lean_ctor_set(v___x_645_, 2, v___y_632_);
lean_inc_ref(v___y_644_);
v___x_646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_646_, 0, v___y_627_);
lean_ctor_set(v___x_646_, 1, v___y_644_);
lean_inc_ref_n(v___x_645_, 12);
v___x_647_ = l_Lean_Syntax_node1(v___y_627_, v___y_625_, v___x_645_);
v___x_648_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0));
lean_inc_ref(v___y_633_);
v___x_649_ = l_Lean_Name_mkStr2(v___y_633_, v___x_648_);
v___x_650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_650_, 0, v___y_627_);
lean_ctor_set(v___x_650_, 1, v___x_648_);
v___x_651_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2));
v___x_652_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3));
v___x_653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_653_, 0, v___y_627_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_Syntax_node1(v___y_627_, v___x_651_, v___x_653_);
v___x_655_ = l_Lean_Syntax_node1(v___y_627_, v___y_621_, v___x_654_);
v___x_656_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4));
v___x_657_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_657_, 0, v___y_627_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5));
v___x_659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_659_, 0, v___y_627_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
lean_inc_ref(v___y_635_);
v___x_660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_660_, 0, v___y_627_);
lean_ctor_set(v___x_660_, 1, v___y_635_);
v___x_661_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6));
v___x_662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_662_, 0, v___y_627_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = l_Lean_Syntax_node1(v___y_627_, v___x_651_, v___x_662_);
v___x_664_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7));
v___x_665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_665_, 0, v___y_627_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
lean_inc_ref(v___x_660_);
v___x_666_ = l_Lean_Syntax_node5(v___y_627_, v___y_621_, v___x_657_, v___x_659_, v___x_660_, v___x_663_, v___x_665_);
v___x_667_ = l_Lean_Syntax_node4(v___y_627_, v___x_649_, v___x_650_, v___x_645_, v___x_655_, v___x_666_);
v___x_668_ = l_Lean_Syntax_node2(v___y_627_, v___y_641_, v___x_647_, v___x_667_);
v___x_669_ = l_Lean_Syntax_node1(v___y_627_, v___y_621_, v___x_668_);
lean_inc_ref(v___y_624_);
v___x_670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_670_, 0, v___y_627_);
lean_ctor_set(v___x_670_, 1, v___y_624_);
v___x_671_ = l_Lean_Syntax_node3(v___y_627_, v___y_634_, v___x_646_, v___x_669_, v___x_670_);
v___x_672_ = l_Lean_Syntax_node1(v___y_627_, v___y_621_, v___x_671_);
v___x_673_ = l_Lean_Syntax_node7(v___y_627_, v___y_629_, v___x_645_, v___x_672_, v___x_645_, v___x_645_, v___x_645_, v___x_645_, v___x_645_);
v___x_674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_674_, 0, v___y_627_);
lean_ctor_set(v___x_674_, 1, v___y_638_);
v___x_675_ = lean_array_push(v___y_622_, v___y_630_);
v___x_676_ = lean_array_push(v___x_675_, v___y_631_);
v___x_677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_677_, 0, v___y_623_);
lean_ctor_set(v___x_677_, 1, v___y_643_);
lean_ctor_set(v___x_677_, 2, v___x_676_);
v___x_678_ = l_Lean_Syntax_node2(v___y_627_, v___y_642_, v___x_645_, v___x_645_);
v___x_679_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9));
v___x_680_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10));
v___x_681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_681_, 0, v___y_627_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = l_Lean_Syntax_node1(v___y_627_, v___x_679_, v___x_681_);
v___x_683_ = l_Lean_Syntax_node2(v___y_627_, v___y_628_, v___x_645_, v___x_645_);
v___x_684_ = l_Lean_Syntax_node4(v___y_627_, v___y_626_, v___x_660_, v___x_682_, v___x_683_, v___x_645_);
v___x_685_ = l_Lean_Syntax_node4(v___y_627_, v___y_640_, v___x_674_, v___x_677_, v___x_678_, v___x_684_);
v___x_686_ = l_Lean_Syntax_node2(v___y_627_, v___y_637_, v___x_673_, v___x_685_);
v___x_687_ = l_Lean_Elab_Command_elabCommand(v___x_686_, v___y_636_, v___y_639_);
lean_dec_ref(v___y_636_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed(lean_object* v_stx_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(v_stx_1193_, v_a_1194_, v_a_1195_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(lean_object* v_00_u03b1_1198_, lean_object* v_ref_1199_, lean_object* v_msg_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_1199_, v_msg_1200_, v___y_1201_, v___y_1202_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___boxed(lean_object* v_00_u03b1_1205_, lean_object* v_ref_1206_, lean_object* v_msg_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(v_00_u03b1_1205_, v_ref_1206_, v_msg_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v_ref_1206_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(lean_object* v_msgData_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msgData_1212_, v___y_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(v_msgData_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(lean_object* v_00_u03b1_1222_, lean_object* v_msg_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_1223_, v___y_1224_, v___y_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_msg_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(v_00_u03b1_1228_, v_msg_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(lean_object* v_msgData_1234_, lean_object* v_macroStack_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_1234_, v_macroStack_1235_, v___y_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1240_, lean_object* v_macroStack_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(v_msgData_1240_, v_macroStack_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1(){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1274_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1275_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12));
v___x_1276_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10));
v___x_1277_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed), 4, 0);
v___x_1278_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1274_, v___x_1275_, v___x_1276_, v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___boxed(lean_object* v_a_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
return v_res_1280_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3));
v___x_1289_ = l_String_toRawSubstring_x27(v___x_1288_);
return v___x_1289_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6));
v___x_1294_ = l_String_toRawSubstring_x27(v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12));
v___x_1307_ = l_String_toRawSubstring_x27(v___x_1306_);
return v___x_1307_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15));
v___x_1312_ = l_String_toRawSubstring_x27(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21));
v___x_1320_ = l_String_toRawSubstring_x27(v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(lean_object* v_stx_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___x_1371_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; uint8_t v___x_1391_; 
v___x_1371_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1));
lean_inc(v_stx_1345_);
v___x_1391_ = l_Lean_Syntax_isOfKind(v_stx_1345_, v___x_1371_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1393_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1345_, v___x_1392_, v_a_1346_, v_a_1347_);
lean_dec(v_stx_1345_);
return v___x_1393_;
}
else
{
lean_object* v___x_1394_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; uint8_t v___y_1529_; lean_object* v_wds_x3f_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v_wds_x3f_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v_pkg_x3f_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v_attrs_x3f_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v_doc_x3f_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1778_ = l_Lean_Syntax_getArg(v_stx_1345_, v___x_1394_);
v___x_1779_ = l_Lean_Syntax_isNone(v___x_1778_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1778_);
v___x_1781_ = l_Lean_Syntax_matchesNull(v___x_1778_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec(v___x_1778_);
v___x_1782_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1783_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1345_, v___x_1782_, v_a_1346_, v_a_1347_);
lean_dec(v_stx_1345_);
return v___x_1783_;
}
else
{
lean_object* v_doc_x3f_1784_; lean_object* v___x_1785_; 
v_doc_x3f_1784_ = l_Lean_Syntax_getArg(v___x_1778_, v___x_1394_);
lean_dec(v___x_1778_);
v___x_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_doc_x3f_1784_);
v_doc_x3f_1766_ = v___x_1785_;
v___y_1767_ = v_a_1346_;
v___y_1768_ = v_a_1347_;
goto v___jp_1765_;
}
}
else
{
lean_object* v___x_1786_; 
lean_dec(v___x_1778_);
v___x_1786_ = lean_box(0);
v_doc_x3f_1766_ = v___x_1786_;
v___y_1767_ = v_a_1346_;
v___y_1768_ = v_a_1347_;
goto v___jp_1765_;
}
v___jp_1395_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_inc_ref_n(v___y_1403_, 2);
v___x_1417_ = l_Array_append___redArg(v___y_1403_, v___y_1416_);
lean_dec_ref(v___y_1416_);
lean_inc_n(v___y_1414_, 8);
lean_inc_n(v___y_1411_, 41);
v___x_1418_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1418_, 0, v___y_1411_);
lean_ctor_set(v___x_1418_, 1, v___y_1414_);
lean_ctor_set(v___x_1418_, 2, v___x_1417_);
v___x_1419_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15));
lean_inc_ref_n(v___y_1408_, 9);
lean_inc_ref_n(v___y_1407_, 13);
lean_inc_ref_n(v___y_1401_, 13);
v___x_1420_ = l_Lean_Name_mkStr4(v___y_1401_, v___y_1407_, v___y_1408_, v___x_1419_);
v___x_1421_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16));
v___x_1422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___y_1411_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39));
v___x_1424_ = l_Lean_Syntax_SepArray_ofElems(v___x_1423_, v___y_1412_);
lean_dec_ref(v___y_1412_);
v___x_1425_ = l_Array_append___redArg(v___y_1403_, v___x_1424_);
lean_dec_ref(v___x_1424_);
v___x_1426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1426_, 0, v___y_1411_);
lean_ctor_set(v___x_1426_, 1, v___y_1414_);
lean_ctor_set(v___x_1426_, 2, v___x_1425_);
v___x_1427_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17));
v___x_1428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___y_1411_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = l_Lean_Syntax_node3(v___y_1411_, v___x_1420_, v___x_1422_, v___x_1426_, v___x_1428_);
v___x_1430_ = l_Lean_Syntax_node1(v___y_1411_, v___y_1414_, v___x_1429_);
lean_inc_n(v___y_1402_, 21);
v___x_1431_ = l_Lean_Syntax_node7(v___y_1411_, v___y_1398_, v___x_1418_, v___x_1430_, v___y_1402_, v___y_1402_, v___y_1402_, v___y_1402_, v___y_1402_);
v___x_1432_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5));
lean_inc_ref_n(v___y_1399_, 3);
v___x_1433_ = l_Lean_Name_mkStr4(v___y_1401_, v___y_1407_, v___y_1399_, v___x_1432_);
v___x_1434_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6));
v___x_1435_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___y_1411_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_1437_ = l_Lean_Name_mkStr4(v___y_1401_, v___y_1407_, v___y_1399_, v___x_1436_);
v___x_1438_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4);
v___x_1439_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5));
lean_inc_n(v___y_1400_, 3);
lean_inc_n(v___y_1409_, 3);
v___x_1440_ = l_Lean_addMacroScope(v___y_1409_, v___x_1439_, v___y_1400_);
lean_inc_n(v___y_1397_, 4);
v___x_1441_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1441_, 0, v___y_1411_);
lean_ctor_set(v___x_1441_, 1, v___x_1438_);
lean_ctor_set(v___x_1441_, 2, v___x_1440_);
lean_ctor_set(v___x_1441_, 3, v___y_1397_);
v___x_1442_ = l_Lean_Syntax_node2(v___y_1411_, v___x_1437_, v___x_1441_, v___y_1402_);
v___x_1443_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_1444_ = l_Lean_Name_mkStr4(v___y_1401_, v___y_1407_, v___y_1399_, v___x_1443_);
v___x_1445_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_1446_ = l_Lean_Name_mkStr4(v___y_1401_, v___y_1407_, v___y_1408_, v___x_1445_);
v___x_1447_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_1448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___y_1411_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v___x_1449_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7);
v___x_1450_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8));
v___x_1451_ = l_Lean_addMacroScope(v___y_1409_, v___x_1450_, v___y_1400_);
v___x_1452_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10));
v___x_1453_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11));
v___x_1454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v___y_1397_);
v___x_1455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1452_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1456_, 0, v___y_1411_);
lean_ctor_set(v___x_1456_, 1, v___x_1449_);
lean_ctor_set(v___x_1456_, 2, v___x_1451_);
lean_ctor_set(v___x_1456_, 3, v___x_1455_);
v___x_1457_ = l_Lean_Syntax_node2(v___y_1411_, v___x_1446_, v___x_1448_, v___x_1456_);
v___x_1458_ = l_Lean_Syntax_node1(v___y_1411_, v___y_1414_, v___x_1457_);
v___x_1459_ = l_Lean_Syntax_node2(v___y_1411_, v___x_1444_, v___y_1402_, v___x_1458_);
v___x_1460_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38));
v___x_1461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___y_1411_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___x_1463_ = l_Lean_Name_mkStr4(v___y_1401_, v___y_1407_, v___y_1408_, v___x_1462_);
v___x_1464_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31));
v___x_1465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___y_1411_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31));
v___x_1467_ = l_Lean_Name_mkStr4(v___y_1401_, v___y_1407_, v___y_1408_, v___x_1466_);
v___x_1468_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32));
v___x_1469_ = l_Lean_Name_mkStr4(v___y_1401_, v___y_1407_, v___y_1408_, v___x_1468_);
v___x_1470_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33));
v___x_1471_ = l_Lean_Name_mkStr4(v___y_1401_, v___y_1407_, v___y_1408_, v___x_1470_);
v___x_1472_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13);
v___x_1473_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14));
v___x_1474_ = l_Lean_addMacroScope(v___y_1409_, v___x_1473_, v___y_1400_);
v___x_1475_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1475_, 0, v___y_1411_);
lean_ctor_set(v___x_1475_, 1, v___x_1472_);
lean_ctor_set(v___x_1475_, 2, v___x_1474_);
lean_ctor_set(v___x_1475_, 3, v___y_1397_);
lean_inc(v___x_1471_);
v___x_1476_ = l_Lean_Syntax_node2(v___y_1411_, v___x_1471_, v___x_1475_, v___y_1402_);
v___x_1477_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37));
v___x_1478_ = l_Lean_Name_mkStr4(v___y_1401_, v___y_1407_, v___y_1408_, v___x_1477_);
v___x_1479_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9));
v___x_1480_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10));
v___x_1481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___y_1411_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = l_Lean_Syntax_node1(v___y_1411_, v___x_1479_, v___x_1481_);
lean_inc_ref_n(v___x_1461_, 2);
lean_inc(v___x_1478_);
v___x_1483_ = l_Lean_Syntax_node3(v___y_1411_, v___x_1478_, v___x_1461_, v___y_1402_, v___x_1482_);
v___x_1484_ = l_Lean_Syntax_node3(v___y_1411_, v___y_1414_, v___y_1402_, v___y_1402_, v___x_1483_);
lean_inc(v___x_1469_);
v___x_1485_ = l_Lean_Syntax_node2(v___y_1411_, v___x_1469_, v___x_1476_, v___x_1484_);
v___x_1486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___y_1411_);
lean_ctor_set(v___x_1486_, 1, v___x_1423_);
v___x_1487_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16);
v___x_1488_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17));
v___x_1489_ = l_Lean_addMacroScope(v___y_1409_, v___x_1488_, v___y_1400_);
v___x_1490_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1490_, 0, v___y_1411_);
lean_ctor_set(v___x_1490_, 1, v___x_1487_);
lean_ctor_set(v___x_1490_, 2, v___x_1489_);
lean_ctor_set(v___x_1490_, 3, v___y_1397_);
v___x_1491_ = l_Lean_Syntax_node2(v___y_1411_, v___x_1471_, v___x_1490_, v___y_1402_);
v___x_1492_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18));
v___x_1493_ = l_Lean_Name_mkStr4(v___y_1401_, v___y_1407_, v___y_1408_, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___y_1411_);
lean_ctor_set(v___x_1494_, 1, v___x_1492_);
v___x_1495_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19));
v___x_1496_ = l_Lean_Name_mkStr4(v___y_1401_, v___y_1407_, v___y_1408_, v___x_1495_);
v___x_1497_ = l_Lean_Syntax_node1(v___y_1411_, v___y_1414_, v___y_1405_);
v___x_1498_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20));
v___x_1499_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___y_1411_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___x_1500_ = l_Lean_Syntax_node4(v___y_1411_, v___x_1496_, v___x_1497_, v___y_1402_, v___x_1499_, v___y_1396_);
v___x_1501_ = l_Lean_Syntax_node2(v___y_1411_, v___x_1493_, v___x_1494_, v___x_1500_);
v___x_1502_ = l_Lean_Syntax_node3(v___y_1411_, v___x_1478_, v___x_1461_, v___y_1402_, v___x_1501_);
v___x_1503_ = l_Lean_Syntax_node3(v___y_1411_, v___y_1414_, v___y_1402_, v___y_1402_, v___x_1502_);
v___x_1504_ = l_Lean_Syntax_node2(v___y_1411_, v___x_1469_, v___x_1491_, v___x_1503_);
v___x_1505_ = l_Lean_Syntax_node3(v___y_1411_, v___y_1414_, v___x_1485_, v___x_1486_, v___x_1504_);
v___x_1506_ = l_Lean_Syntax_node1(v___y_1411_, v___x_1467_, v___x_1505_);
v___x_1507_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49));
v___x_1508_ = l_Lean_Name_mkStr4(v___y_1401_, v___y_1407_, v___y_1408_, v___x_1507_);
v___x_1509_ = l_Lean_Syntax_node1(v___y_1411_, v___x_1508_, v___y_1402_);
v___x_1510_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50));
v___x_1511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___y_1411_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = l_Lean_Syntax_node6(v___y_1411_, v___x_1463_, v___x_1465_, v___y_1402_, v___x_1506_, v___x_1509_, v___y_1402_, v___x_1511_);
lean_inc(v___y_1410_);
v___x_1513_ = l_Lean_Syntax_node2(v___y_1411_, v___y_1410_, v___y_1402_, v___y_1402_);
if (lean_obj_tag(v___y_1415_) == 1)
{
lean_object* v_val_1514_; lean_object* v___x_1515_; 
v_val_1514_ = lean_ctor_get(v___y_1415_, 0);
lean_inc(v_val_1514_);
lean_dec_ref_known(v___y_1415_, 1);
v___x_1515_ = l_Array_mkArray1___redArg(v_val_1514_);
v___y_1349_ = v___x_1461_;
v___y_1350_ = v___x_1459_;
v___y_1351_ = v___x_1512_;
v___y_1352_ = v___x_1442_;
v___y_1353_ = v___y_1402_;
v___y_1354_ = v___y_1403_;
v___y_1355_ = v___y_1404_;
v___y_1356_ = v___y_1406_;
v___y_1357_ = v___x_1435_;
v___y_1358_ = v___x_1433_;
v___y_1359_ = v___y_1411_;
v___y_1360_ = v___x_1513_;
v___y_1361_ = v___y_1413_;
v___y_1362_ = v___x_1431_;
v___y_1363_ = v___y_1414_;
v___y_1364_ = v___x_1515_;
goto v___jp_1348_;
}
else
{
lean_object* v___x_1516_; 
lean_dec(v___y_1415_);
v___x_1516_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
v___y_1349_ = v___x_1461_;
v___y_1350_ = v___x_1459_;
v___y_1351_ = v___x_1512_;
v___y_1352_ = v___x_1442_;
v___y_1353_ = v___y_1402_;
v___y_1354_ = v___y_1403_;
v___y_1355_ = v___y_1404_;
v___y_1356_ = v___y_1406_;
v___y_1357_ = v___x_1435_;
v___y_1358_ = v___x_1433_;
v___y_1359_ = v___y_1411_;
v___y_1360_ = v___x_1513_;
v___y_1361_ = v___y_1413_;
v___y_1362_ = v___x_1431_;
v___y_1363_ = v___y_1414_;
v___y_1364_ = v___x_1516_;
goto v___jp_1348_;
}
}
v___jp_1517_:
{
lean_object* v_methods_1533_; lean_object* v_quotContext_1534_; lean_object* v_currMacroScope_1535_; lean_object* v_currRecDepth_1536_; lean_object* v_maxRecDepth_1537_; lean_object* v_ref_1538_; lean_object* v_ref_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_methods_1533_ = lean_ctor_get(v___y_1531_, 0);
v_quotContext_1534_ = lean_ctor_get(v___y_1531_, 1);
v_currMacroScope_1535_ = lean_ctor_get(v___y_1531_, 2);
v_currRecDepth_1536_ = lean_ctor_get(v___y_1531_, 3);
v_maxRecDepth_1537_ = lean_ctor_get(v___y_1531_, 4);
v_ref_1538_ = lean_ctor_get(v___y_1531_, 5);
v_ref_1539_ = l_Lean_replaceRef(v___y_1526_, v_ref_1538_);
lean_dec(v___y_1526_);
lean_inc(v_ref_1539_);
lean_inc(v_maxRecDepth_1537_);
lean_inc(v_currRecDepth_1536_);
lean_inc(v_currMacroScope_1535_);
lean_inc(v_quotContext_1534_);
lean_inc(v_methods_1533_);
v___x_1540_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1540_, 0, v_methods_1533_);
lean_ctor_set(v___x_1540_, 1, v_quotContext_1534_);
lean_ctor_set(v___x_1540_, 2, v_currMacroScope_1535_);
lean_ctor_set(v___x_1540_, 3, v_currRecDepth_1536_);
lean_ctor_set(v___x_1540_, 4, v_maxRecDepth_1537_);
lean_ctor_set(v___x_1540_, 5, v_ref_1539_);
v___x_1541_ = l_Lake_DSL_expandOptSimpleBinder(v___y_1523_, v___x_1540_, v___y_1532_);
lean_dec_ref_known(v___x_1540_, 6);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v_a_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
v_a_1543_ = lean_ctor_get(v___x_1541_, 1);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1541_, 2);
v___x_1544_ = l_Lean_SourceInfo_fromRef(v_ref_1539_, v___y_1529_);
lean_dec(v_ref_1539_);
v___x_1545_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_1546_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51));
lean_inc_ref_n(v___y_1522_, 5);
lean_inc_ref_n(v___y_1527_, 5);
v___x_1547_ = l_Lean_Name_mkStr4(v___y_1527_, v___y_1522_, v___x_1545_, v___x_1546_);
v___x_1548_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52));
v___x_1549_ = l_Lean_Name_mkStr4(v___y_1527_, v___y_1522_, v___x_1545_, v___x_1548_);
v___x_1550_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_1551_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___x_1544_, 5);
v___x_1552_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1544_);
lean_ctor_set(v___x_1552_, 1, v___x_1550_);
lean_ctor_set(v___x_1552_, 2, v___x_1551_);
lean_inc_ref_n(v___x_1552_, 2);
v___x_1553_ = l_Lean_Syntax_node1(v___x_1544_, v___x_1549_, v___x_1552_);
v___x_1554_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57));
v___x_1555_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58));
v___x_1556_ = l_Lean_Name_mkStr4(v___y_1527_, v___y_1522_, v___x_1554_, v___x_1555_);
v___x_1557_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22);
v___x_1558_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24));
lean_inc(v_currMacroScope_1535_);
lean_inc(v_quotContext_1534_);
v___x_1559_ = l_Lean_addMacroScope(v_quotContext_1534_, v___x_1558_, v_currMacroScope_1535_);
v___x_1560_ = lean_box(0);
v___x_1561_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1544_);
lean_ctor_set(v___x_1561_, 1, v___x_1557_);
lean_ctor_set(v___x_1561_, 2, v___x_1559_);
lean_ctor_set(v___x_1561_, 3, v___x_1560_);
v___x_1562_ = l_Lean_Syntax_node2(v___x_1544_, v___x_1556_, v___x_1561_, v___x_1552_);
v___x_1563_ = l_Lean_Syntax_node2(v___x_1544_, v___x_1547_, v___x_1553_, v___x_1562_);
v___x_1564_ = lean_mk_empty_array_with_capacity(v___y_1528_);
v___x_1565_ = lean_array_push(v___x_1564_, v___x_1563_);
v___x_1566_ = l_Lake_DSL_expandAttrs(v___y_1521_);
v___x_1567_ = l_Array_append___redArg(v___x_1565_, v___x_1566_);
lean_dec_ref(v___x_1566_);
v___x_1568_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_1524_, 2);
v___x_1569_ = l_Lean_Name_mkStr4(v___y_1527_, v___y_1522_, v___y_1524_, v___x_1568_);
v___x_1570_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_1571_ = l_Lean_Name_mkStr4(v___y_1527_, v___y_1522_, v___y_1524_, v___x_1570_);
if (lean_obj_tag(v___y_1518_) == 1)
{
lean_object* v_val_1572_; lean_object* v___x_1573_; 
v_val_1572_ = lean_ctor_get(v___y_1518_, 0);
lean_inc(v_val_1572_);
lean_dec_ref_known(v___y_1518_, 1);
v___x_1573_ = l_Array_mkArray1___redArg(v_val_1572_);
lean_inc(v_quotContext_1534_);
lean_inc(v_currMacroScope_1535_);
v___y_1396_ = v___y_1519_;
v___y_1397_ = v___x_1560_;
v___y_1398_ = v___x_1571_;
v___y_1399_ = v___y_1524_;
v___y_1400_ = v_currMacroScope_1535_;
v___y_1401_ = v___y_1527_;
v___y_1402_ = v___x_1552_;
v___y_1403_ = v___x_1551_;
v___y_1404_ = v___y_1520_;
v___y_1405_ = v_a_1542_;
v___y_1406_ = v_a_1543_;
v___y_1407_ = v___y_1522_;
v___y_1408_ = v___x_1545_;
v___y_1409_ = v_quotContext_1534_;
v___y_1410_ = v___y_1525_;
v___y_1411_ = v___x_1544_;
v___y_1412_ = v___x_1567_;
v___y_1413_ = v___x_1569_;
v___y_1414_ = v___x_1550_;
v___y_1415_ = v_wds_x3f_1530_;
v___y_1416_ = v___x_1573_;
goto v___jp_1395_;
}
else
{
lean_object* v___x_1574_; 
lean_dec(v___y_1518_);
v___x_1574_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
lean_inc(v_quotContext_1534_);
lean_inc(v_currMacroScope_1535_);
v___y_1396_ = v___y_1519_;
v___y_1397_ = v___x_1560_;
v___y_1398_ = v___x_1571_;
v___y_1399_ = v___y_1524_;
v___y_1400_ = v_currMacroScope_1535_;
v___y_1401_ = v___y_1527_;
v___y_1402_ = v___x_1552_;
v___y_1403_ = v___x_1551_;
v___y_1404_ = v___y_1520_;
v___y_1405_ = v_a_1542_;
v___y_1406_ = v_a_1543_;
v___y_1407_ = v___y_1522_;
v___y_1408_ = v___x_1545_;
v___y_1409_ = v_quotContext_1534_;
v___y_1410_ = v___y_1525_;
v___y_1411_ = v___x_1544_;
v___y_1412_ = v___x_1567_;
v___y_1413_ = v___x_1569_;
v___y_1414_ = v___x_1550_;
v___y_1415_ = v_wds_x3f_1530_;
v___y_1416_ = v___x_1574_;
goto v___jp_1395_;
}
}
else
{
lean_object* v_a_1575_; lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_ref_1539_);
lean_dec(v_wds_x3f_1530_);
lean_dec(v___y_1521_);
lean_dec(v___y_1519_);
lean_dec(v___y_1518_);
v_a_1575_ = lean_ctor_get(v___x_1541_, 0);
v_a_1576_ = lean_ctor_get(v___x_1541_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1541_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_inc(v_a_1575_);
lean_dec(v___x_1541_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1575_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
v___jp_1584_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_inc_ref_n(v___y_1597_, 2);
v___x_1599_ = l_Array_append___redArg(v___y_1597_, v___y_1598_);
lean_dec_ref(v___y_1598_);
lean_inc_n(v___y_1589_, 2);
lean_inc_n(v___y_1585_, 6);
v___x_1600_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1600_, 0, v___y_1585_);
lean_ctor_set(v___x_1600_, 1, v___y_1589_);
lean_ctor_set(v___x_1600_, 2, v___x_1599_);
v___x_1601_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_1602_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25));
lean_inc_ref_n(v___y_1588_, 2);
lean_inc_ref_n(v___y_1590_, 2);
v___x_1603_ = l_Lean_Name_mkStr4(v___y_1590_, v___y_1588_, v___x_1601_, v___x_1602_);
v___x_1604_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38));
v___x_1605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___y_1585_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
lean_inc_ref(v___y_1586_);
v___x_1606_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___y_1585_);
lean_ctor_set(v___x_1606_, 1, v___y_1586_);
lean_inc(v___y_1594_);
v___x_1607_ = l_Lean_Syntax_node2(v___y_1585_, v___y_1594_, v___x_1606_, v___y_1593_);
v___x_1608_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26));
v___x_1609_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27));
v___x_1610_ = l_Lean_Name_mkStr4(v___y_1590_, v___y_1588_, v___x_1608_, v___x_1609_);
v___x_1611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1611_, 0, v___y_1585_);
lean_ctor_set(v___x_1611_, 1, v___y_1589_);
lean_ctor_set(v___x_1611_, 2, v___y_1597_);
lean_inc_ref(v___x_1611_);
v___x_1612_ = l_Lean_Syntax_node2(v___y_1585_, v___x_1610_, v___x_1611_, v___x_1611_);
if (lean_obj_tag(v___y_1591_) == 1)
{
lean_object* v_val_1613_; lean_object* v___x_1614_; 
v_val_1613_ = lean_ctor_get(v___y_1591_, 0);
lean_inc(v_val_1613_);
lean_dec_ref_known(v___y_1591_, 1);
v___x_1614_ = l_Array_mkArray1___redArg(v_val_1613_);
v___y_1373_ = v___x_1603_;
v___y_1374_ = v___x_1607_;
v___y_1375_ = v___y_1585_;
v___y_1376_ = v___x_1612_;
v___y_1377_ = v___x_1605_;
v___y_1378_ = v___y_1589_;
v___y_1379_ = v___y_1592_;
v___y_1380_ = v___y_1587_;
v___y_1381_ = v___y_1595_;
v___y_1382_ = v___y_1596_;
v___y_1383_ = v___x_1600_;
v___y_1384_ = v___y_1597_;
v___y_1385_ = v___x_1614_;
goto v___jp_1372_;
}
else
{
lean_object* v___x_1615_; 
lean_dec(v___y_1591_);
v___x_1615_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
v___y_1373_ = v___x_1603_;
v___y_1374_ = v___x_1607_;
v___y_1375_ = v___y_1585_;
v___y_1376_ = v___x_1612_;
v___y_1377_ = v___x_1605_;
v___y_1378_ = v___y_1589_;
v___y_1379_ = v___y_1592_;
v___y_1380_ = v___y_1587_;
v___y_1381_ = v___y_1595_;
v___y_1382_ = v___y_1596_;
v___y_1383_ = v___x_1600_;
v___y_1384_ = v___y_1597_;
v___y_1385_ = v___x_1615_;
goto v___jp_1372_;
}
}
v___jp_1616_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_inc_ref(v___y_1629_);
v___x_1631_ = l_Array_append___redArg(v___y_1629_, v___y_1630_);
lean_dec_ref(v___y_1630_);
lean_inc(v___y_1622_);
lean_inc(v___y_1617_);
v___x_1632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1632_, 0, v___y_1617_);
lean_ctor_set(v___x_1632_, 1, v___y_1622_);
lean_ctor_set(v___x_1632_, 2, v___x_1631_);
v___x_1633_ = l_Lean_SourceInfo_fromRef(v___y_1624_, v___x_1391_);
lean_dec(v___y_1624_);
v___x_1634_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23));
v___x_1635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
if (lean_obj_tag(v___y_1618_) == 1)
{
lean_object* v_val_1636_; lean_object* v___x_1637_; 
v_val_1636_ = lean_ctor_get(v___y_1618_, 0);
lean_inc(v_val_1636_);
lean_dec_ref_known(v___y_1618_, 1);
v___x_1637_ = l_Array_mkArray1___redArg(v_val_1636_);
v___y_1585_ = v___y_1617_;
v___y_1586_ = v___y_1619_;
v___y_1587_ = v___y_1620_;
v___y_1588_ = v___y_1621_;
v___y_1589_ = v___y_1622_;
v___y_1590_ = v___y_1623_;
v___y_1591_ = v___y_1625_;
v___y_1592_ = v___y_1626_;
v___y_1593_ = v___y_1627_;
v___y_1594_ = v___y_1628_;
v___y_1595_ = v___x_1635_;
v___y_1596_ = v___x_1632_;
v___y_1597_ = v___y_1629_;
v___y_1598_ = v___x_1637_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1638_; 
lean_dec(v___y_1618_);
v___x_1638_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
v___y_1585_ = v___y_1617_;
v___y_1586_ = v___y_1619_;
v___y_1587_ = v___y_1620_;
v___y_1588_ = v___y_1621_;
v___y_1589_ = v___y_1622_;
v___y_1590_ = v___y_1623_;
v___y_1591_ = v___y_1625_;
v___y_1592_ = v___y_1626_;
v___y_1593_ = v___y_1627_;
v___y_1594_ = v___y_1628_;
v___y_1595_ = v___x_1635_;
v___y_1596_ = v___x_1632_;
v___y_1597_ = v___y_1629_;
v___y_1598_ = v___x_1638_;
goto v___jp_1584_;
}
}
v___jp_1639_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_inc_ref(v___y_1652_);
v___x_1654_ = l_Array_append___redArg(v___y_1652_, v___y_1653_);
lean_dec_ref(v___y_1653_);
lean_inc(v___y_1645_);
lean_inc(v___y_1640_);
v___x_1655_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1655_, 0, v___y_1640_);
lean_ctor_set(v___x_1655_, 1, v___y_1645_);
lean_ctor_set(v___x_1655_, 2, v___x_1654_);
if (lean_obj_tag(v___y_1643_) == 1)
{
lean_object* v_val_1656_; lean_object* v___x_1657_; 
v_val_1656_ = lean_ctor_get(v___y_1643_, 0);
lean_inc(v_val_1656_);
lean_dec_ref_known(v___y_1643_, 1);
v___x_1657_ = l_Array_mkArray1___redArg(v_val_1656_);
v___y_1617_ = v___y_1640_;
v___y_1618_ = v___y_1641_;
v___y_1619_ = v___y_1642_;
v___y_1620_ = v___x_1655_;
v___y_1621_ = v___y_1644_;
v___y_1622_ = v___y_1645_;
v___y_1623_ = v___y_1646_;
v___y_1624_ = v___y_1647_;
v___y_1625_ = v___y_1648_;
v___y_1626_ = v___y_1649_;
v___y_1627_ = v___y_1650_;
v___y_1628_ = v___y_1651_;
v___y_1629_ = v___y_1652_;
v___y_1630_ = v___x_1657_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1658_; 
lean_dec(v___y_1643_);
v___x_1658_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
v___y_1617_ = v___y_1640_;
v___y_1618_ = v___y_1641_;
v___y_1619_ = v___y_1642_;
v___y_1620_ = v___x_1655_;
v___y_1621_ = v___y_1644_;
v___y_1622_ = v___y_1645_;
v___y_1623_ = v___y_1646_;
v___y_1624_ = v___y_1647_;
v___y_1625_ = v___y_1648_;
v___y_1626_ = v___y_1649_;
v___y_1627_ = v___y_1650_;
v___y_1628_ = v___y_1651_;
v___y_1629_ = v___y_1652_;
v___y_1630_ = v___x_1658_;
goto v___jp_1616_;
}
}
v___jp_1659_:
{
lean_object* v_ref_1672_; uint8_t v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_ref_1672_ = lean_ctor_get(v___y_1670_, 5);
v___x_1673_ = 0;
v___x_1674_ = l_Lean_SourceInfo_fromRef(v_ref_1672_, v___x_1673_);
v___x_1675_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_1676_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
if (lean_obj_tag(v___y_1660_) == 1)
{
lean_object* v_val_1677_; lean_object* v___x_1678_; 
v_val_1677_ = lean_ctor_get(v___y_1660_, 0);
lean_inc(v_val_1677_);
lean_dec_ref_known(v___y_1660_, 1);
v___x_1678_ = l_Array_mkArray1___redArg(v_val_1677_);
v___y_1640_ = v___x_1674_;
v___y_1641_ = v___y_1663_;
v___y_1642_ = v___y_1664_;
v___y_1643_ = v___y_1661_;
v___y_1644_ = v___y_1662_;
v___y_1645_ = v___x_1675_;
v___y_1646_ = v___y_1665_;
v___y_1647_ = v___y_1666_;
v___y_1648_ = v_wds_x3f_1669_;
v___y_1649_ = v___y_1671_;
v___y_1650_ = v___y_1667_;
v___y_1651_ = v___y_1668_;
v___y_1652_ = v___x_1676_;
v___y_1653_ = v___x_1678_;
goto v___jp_1639_;
}
else
{
lean_object* v___x_1679_; 
lean_dec(v___y_1660_);
v___x_1679_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
v___y_1640_ = v___x_1674_;
v___y_1641_ = v___y_1663_;
v___y_1642_ = v___y_1664_;
v___y_1643_ = v___y_1661_;
v___y_1644_ = v___y_1662_;
v___y_1645_ = v___x_1675_;
v___y_1646_ = v___y_1665_;
v___y_1647_ = v___y_1666_;
v___y_1648_ = v_wds_x3f_1669_;
v___y_1649_ = v___y_1671_;
v___y_1650_ = v___y_1667_;
v___y_1651_ = v___y_1668_;
v___y_1652_ = v___x_1676_;
v___y_1653_ = v___x_1679_;
goto v___jp_1639_;
}
}
v___jp_1680_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1690_ = lean_unsigned_to_nat(4u);
v___x_1691_ = l_Lean_Syntax_getArg(v_stx_1345_, v___x_1690_);
v___x_1692_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26));
lean_inc(v___x_1691_);
v___x_1693_ = l_Lean_Syntax_isOfKind(v___x_1691_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1694_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1695_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_1696_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_1697_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27));
lean_inc(v___x_1691_);
v___x_1698_ = l_Lean_Syntax_isOfKind(v___x_1691_, v___x_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_dec(v___x_1691_);
lean_dec(v_pkg_x3f_1687_);
lean_dec(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec(v___y_1681_);
v___x_1699_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1700_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1345_, v___x_1699_, v___y_1688_, v___y_1689_);
lean_dec(v_stx_1345_);
return v___x_1700_;
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1701_ = l_Lean_Syntax_getArg(v___x_1691_, v___y_1685_);
v___x_1702_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28));
lean_inc(v___x_1701_);
v___x_1703_ = l_Lean_Syntax_isOfKind(v___x_1701_, v___x_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec(v___x_1701_);
lean_dec(v___x_1691_);
lean_dec(v_pkg_x3f_1687_);
lean_dec(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec(v___y_1681_);
v___x_1704_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1705_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1345_, v___x_1704_, v___y_1688_, v___y_1689_);
lean_dec(v_stx_1345_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = l_Lean_Syntax_getArg(v___x_1701_, v___x_1394_);
v___x_1707_ = l_Lean_Syntax_matchesNull(v___x_1706_, v___x_1394_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec(v___x_1701_);
lean_dec(v___x_1691_);
lean_dec(v_pkg_x3f_1687_);
lean_dec(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec(v___y_1681_);
v___x_1708_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1709_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1345_, v___x_1708_, v___y_1688_, v___y_1689_);
lean_dec(v_stx_1345_);
return v___x_1709_;
}
else
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = l_Lean_Syntax_getArg(v___x_1701_, v___y_1686_);
lean_dec(v___x_1701_);
v___x_1711_ = l_Lean_Syntax_matchesNull(v___x_1710_, v___x_1394_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_dec(v___x_1691_);
lean_dec(v_pkg_x3f_1687_);
lean_dec(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec(v___y_1681_);
v___x_1712_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1713_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1345_, v___x_1712_, v___y_1688_, v___y_1689_);
lean_dec(v_stx_1345_);
return v___x_1713_;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1714_ = l_Lean_Syntax_getArg(v___x_1691_, v___y_1686_);
v___x_1715_ = l_Lean_Syntax_getArg(v___x_1691_, v___y_1684_);
lean_dec(v___x_1691_);
v___x_1716_ = l_Lean_Syntax_isNone(v___x_1715_);
if (v___x_1716_ == 0)
{
uint8_t v___x_1717_; 
lean_inc(v___x_1715_);
v___x_1717_ = l_Lean_Syntax_matchesNull(v___x_1715_, v___y_1686_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec(v___x_1715_);
lean_dec(v___x_1714_);
lean_dec(v_pkg_x3f_1687_);
lean_dec(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec(v___y_1681_);
v___x_1718_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1719_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1345_, v___x_1718_, v___y_1688_, v___y_1689_);
lean_dec(v_stx_1345_);
return v___x_1719_;
}
else
{
lean_object* v_wds_x3f_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v_wds_x3f_1720_ = l_Lean_Syntax_getArg(v___x_1715_, v___x_1394_);
lean_dec(v___x_1715_);
v___x_1721_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_1720_);
v___x_1722_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1720_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec(v_wds_x3f_1720_);
lean_dec(v___x_1714_);
lean_dec(v_pkg_x3f_1687_);
lean_dec(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec(v___y_1681_);
v___x_1723_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1724_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1345_, v___x_1723_, v___y_1688_, v___y_1689_);
lean_dec(v_stx_1345_);
return v___x_1724_;
}
else
{
lean_object* v___x_1725_; 
lean_dec(v_stx_1345_);
v___x_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_wds_x3f_1720_);
v___y_1518_ = v___y_1681_;
v___y_1519_ = v___x_1714_;
v___y_1520_ = v___x_1697_;
v___y_1521_ = v___y_1682_;
v___y_1522_ = v___x_1695_;
v___y_1523_ = v_pkg_x3f_1687_;
v___y_1524_ = v___x_1696_;
v___y_1525_ = v___x_1702_;
v___y_1526_ = v___y_1683_;
v___y_1527_ = v___x_1694_;
v___y_1528_ = v___y_1686_;
v___y_1529_ = v___x_1693_;
v_wds_x3f_1530_ = v___x_1725_;
v___y_1531_ = v___y_1688_;
v___y_1532_ = v___y_1689_;
goto v___jp_1517_;
}
}
}
else
{
lean_object* v___x_1726_; 
lean_dec(v___x_1715_);
lean_dec(v_stx_1345_);
v___x_1726_ = lean_box(0);
v___y_1518_ = v___y_1681_;
v___y_1519_ = v___x_1714_;
v___y_1520_ = v___x_1697_;
v___y_1521_ = v___y_1682_;
v___y_1522_ = v___x_1695_;
v___y_1523_ = v_pkg_x3f_1687_;
v___y_1524_ = v___x_1696_;
v___y_1525_ = v___x_1702_;
v___y_1526_ = v___y_1683_;
v___y_1527_ = v___x_1694_;
v___y_1528_ = v___y_1686_;
v___y_1529_ = v___x_1693_;
v_wds_x3f_1530_ = v___x_1726_;
v___y_1531_ = v___y_1688_;
v___y_1532_ = v___y_1689_;
goto v___jp_1517_;
}
}
}
}
}
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1727_ = l_Lean_Syntax_getArg(v___x_1691_, v___x_1394_);
v___x_1728_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1729_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_1730_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29));
v___x_1731_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30));
lean_inc(v___x_1727_);
v___x_1732_ = l_Lean_Syntax_isOfKind(v___x_1727_, v___x_1731_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_dec(v___x_1727_);
lean_dec(v___x_1691_);
lean_dec(v_pkg_x3f_1687_);
lean_dec(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec(v___y_1681_);
v___x_1733_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1734_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1345_, v___x_1733_, v___y_1688_, v___y_1689_);
lean_dec(v_stx_1345_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1735_ = l_Lean_Syntax_getArg(v___x_1727_, v___y_1686_);
lean_dec(v___x_1727_);
v___x_1736_ = l_Lean_Syntax_getArg(v___x_1691_, v___y_1686_);
lean_dec(v___x_1691_);
v___x_1737_ = l_Lean_Syntax_isNone(v___x_1736_);
if (v___x_1737_ == 0)
{
uint8_t v___x_1738_; 
lean_inc(v___x_1736_);
v___x_1738_ = l_Lean_Syntax_matchesNull(v___x_1736_, v___y_1686_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec(v___x_1736_);
lean_dec(v___x_1735_);
lean_dec(v_pkg_x3f_1687_);
lean_dec(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec(v___y_1681_);
v___x_1739_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1740_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1345_, v___x_1739_, v___y_1688_, v___y_1689_);
lean_dec(v_stx_1345_);
return v___x_1740_;
}
else
{
lean_object* v_wds_x3f_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v_wds_x3f_1741_ = l_Lean_Syntax_getArg(v___x_1736_, v___x_1394_);
lean_dec(v___x_1736_);
v___x_1742_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_1741_);
v___x_1743_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec(v_wds_x3f_1741_);
lean_dec(v___x_1735_);
lean_dec(v_pkg_x3f_1687_);
lean_dec(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec(v___y_1681_);
v___x_1744_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1745_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1345_, v___x_1744_, v___y_1688_, v___y_1689_);
lean_dec(v_stx_1345_);
return v___x_1745_;
}
else
{
lean_object* v___x_1746_; 
lean_dec(v_stx_1345_);
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_wds_x3f_1741_);
v___y_1660_ = v___y_1681_;
v___y_1661_ = v___y_1682_;
v___y_1662_ = v___x_1729_;
v___y_1663_ = v_pkg_x3f_1687_;
v___y_1664_ = v___x_1730_;
v___y_1665_ = v___x_1728_;
v___y_1666_ = v___y_1683_;
v___y_1667_ = v___x_1735_;
v___y_1668_ = v___x_1731_;
v_wds_x3f_1669_ = v___x_1746_;
v___y_1670_ = v___y_1688_;
v___y_1671_ = v___y_1689_;
goto v___jp_1659_;
}
}
}
else
{
lean_object* v___x_1747_; 
lean_dec(v___x_1736_);
lean_dec(v_stx_1345_);
v___x_1747_ = lean_box(0);
v___y_1660_ = v___y_1681_;
v___y_1661_ = v___y_1682_;
v___y_1662_ = v___x_1729_;
v___y_1663_ = v_pkg_x3f_1687_;
v___y_1664_ = v___x_1730_;
v___y_1665_ = v___x_1728_;
v___y_1666_ = v___y_1683_;
v___y_1667_ = v___x_1735_;
v___y_1668_ = v___x_1731_;
v_wds_x3f_1669_ = v___x_1747_;
v___y_1670_ = v___y_1688_;
v___y_1671_ = v___y_1689_;
goto v___jp_1659_;
}
}
}
}
v___jp_1748_:
{
lean_object* v___x_1754_; lean_object* v_kw_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1754_ = lean_unsigned_to_nat(2u);
v_kw_1755_ = l_Lean_Syntax_getArg(v_stx_1345_, v___x_1754_);
v___x_1756_ = lean_unsigned_to_nat(3u);
v___x_1757_ = l_Lean_Syntax_getArg(v_stx_1345_, v___x_1756_);
v___x_1758_ = l_Lean_Syntax_isNone(v___x_1757_);
if (v___x_1758_ == 0)
{
uint8_t v___x_1759_; 
lean_inc(v___x_1757_);
v___x_1759_ = l_Lean_Syntax_matchesNull(v___x_1757_, v___y_1750_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec(v___x_1757_);
lean_dec(v_kw_1755_);
lean_dec(v_attrs_x3f_1751_);
lean_dec(v___y_1749_);
v___x_1760_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1761_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1345_, v___x_1760_, v___y_1752_, v___y_1753_);
lean_dec(v_stx_1345_);
return v___x_1761_;
}
else
{
lean_object* v_pkg_x3f_1762_; lean_object* v___x_1763_; 
v_pkg_x3f_1762_ = l_Lean_Syntax_getArg(v___x_1757_, v___x_1394_);
lean_dec(v___x_1757_);
v___x_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1763_, 0, v_pkg_x3f_1762_);
v___y_1681_ = v___y_1749_;
v___y_1682_ = v_attrs_x3f_1751_;
v___y_1683_ = v_kw_1755_;
v___y_1684_ = v___x_1756_;
v___y_1685_ = v___x_1754_;
v___y_1686_ = v___y_1750_;
v_pkg_x3f_1687_ = v___x_1763_;
v___y_1688_ = v___y_1752_;
v___y_1689_ = v___y_1753_;
goto v___jp_1680_;
}
}
else
{
lean_object* v___x_1764_; 
lean_dec(v___x_1757_);
v___x_1764_ = lean_box(0);
v___y_1681_ = v___y_1749_;
v___y_1682_ = v_attrs_x3f_1751_;
v___y_1683_ = v_kw_1755_;
v___y_1684_ = v___x_1756_;
v___y_1685_ = v___x_1754_;
v___y_1686_ = v___y_1750_;
v_pkg_x3f_1687_ = v___x_1764_;
v___y_1688_ = v___y_1752_;
v___y_1689_ = v___y_1753_;
goto v___jp_1680_;
}
}
v___jp_1765_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1769_ = lean_unsigned_to_nat(1u);
v___x_1770_ = l_Lean_Syntax_getArg(v_stx_1345_, v___x_1769_);
v___x_1771_ = l_Lean_Syntax_isNone(v___x_1770_);
if (v___x_1771_ == 0)
{
uint8_t v___x_1772_; 
lean_inc(v___x_1770_);
v___x_1772_ = l_Lean_Syntax_matchesNull(v___x_1770_, v___x_1769_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_dec(v___x_1770_);
lean_dec(v_doc_x3f_1766_);
v___x_1773_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1774_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1345_, v___x_1773_, v___y_1767_, v___y_1768_);
lean_dec(v_stx_1345_);
return v___x_1774_;
}
else
{
lean_object* v_attrs_x3f_1775_; lean_object* v___x_1776_; 
v_attrs_x3f_1775_ = l_Lean_Syntax_getArg(v___x_1770_, v___x_1394_);
lean_dec(v___x_1770_);
v___x_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1776_, 0, v_attrs_x3f_1775_);
v___y_1749_ = v_doc_x3f_1766_;
v___y_1750_ = v___x_1769_;
v_attrs_x3f_1751_ = v___x_1776_;
v___y_1752_ = v___y_1767_;
v___y_1753_ = v___y_1768_;
goto v___jp_1748_;
}
}
else
{
lean_object* v___x_1777_; 
lean_dec(v___x_1770_);
v___x_1777_ = lean_box(0);
v___y_1749_ = v_doc_x3f_1766_;
v___y_1750_ = v___x_1769_;
v_attrs_x3f_1751_ = v___x_1777_;
v___y_1752_ = v___y_1767_;
v___y_1753_ = v___y_1768_;
goto v___jp_1748_;
}
}
}
v___jp_1348_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_inc_ref(v___y_1354_);
v___x_1365_ = l_Array_append___redArg(v___y_1354_, v___y_1364_);
lean_dec_ref(v___y_1364_);
lean_inc(v___y_1363_);
lean_inc_n(v___y_1359_, 3);
v___x_1366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1366_, 0, v___y_1359_);
lean_ctor_set(v___x_1366_, 1, v___y_1363_);
lean_ctor_set(v___x_1366_, 2, v___x_1365_);
lean_inc(v___y_1355_);
v___x_1367_ = l_Lean_Syntax_node4(v___y_1359_, v___y_1355_, v___y_1349_, v___y_1351_, v___y_1360_, v___x_1366_);
v___x_1368_ = l_Lean_Syntax_node5(v___y_1359_, v___y_1358_, v___y_1357_, v___y_1352_, v___y_1350_, v___x_1367_, v___y_1353_);
v___x_1369_ = l_Lean_Syntax_node2(v___y_1359_, v___y_1361_, v___y_1362_, v___x_1368_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
lean_ctor_set(v___x_1370_, 1, v___y_1356_);
return v___x_1370_;
}
v___jp_1372_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_inc_ref(v___y_1384_);
v___x_1386_ = l_Array_append___redArg(v___y_1384_, v___y_1385_);
lean_dec_ref(v___y_1385_);
lean_inc(v___y_1378_);
lean_inc_n(v___y_1375_, 2);
v___x_1387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1387_, 0, v___y_1375_);
lean_ctor_set(v___x_1387_, 1, v___y_1378_);
lean_ctor_set(v___x_1387_, 2, v___x_1386_);
v___x_1388_ = l_Lean_Syntax_node4(v___y_1375_, v___y_1373_, v___y_1377_, v___y_1374_, v___y_1376_, v___x_1387_);
v___x_1389_ = l_Lean_Syntax_node5(v___y_1375_, v___x_1371_, v___y_1380_, v___y_1382_, v___y_1381_, v___y_1383_, v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v___y_1379_);
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed(lean_object* v_stx_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(v_stx_1787_, v_a_1788_, v_a_1789_);
lean_dec_ref(v_a_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1(){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1796_ = l_Lean_Elab_macroAttribute;
v___x_1797_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1));
v___x_1798_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1));
v___x_1799_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed), 3, 0);
v___x_1800_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1796_, v___x_1797_, v___x_1798_, v___x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___boxed(lean_object* v_a_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
return v_res_1802_;
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
